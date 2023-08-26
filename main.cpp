#include <fstream>
#include <iostream>
#include <llvm-14/llvm/IR/Verifier.h>
#include <llvm-14/llvm/Support/CodeGen.h>
#include <llvm-14/llvm/Support/FileSystem.h>
#include <llvm-14/llvm/Support/raw_ostream.h>
#include <llvm-14/llvm/Transforms/Scalar.h>
#include <memory>
#include <stack>
#include <stdio.h>
#include <string_view>
#include <unordered_map>

#include <chrono>
#include <fstream>
#include <iostream>
#include <stack>
#include <stdio.h>
#include <string_view>
#include <unordered_map>

#include "llvm/ADT/APFloat.h"
#include "llvm/ADT/Optional.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ExecutionEngine/ExecutionEngine.h"
#include "llvm/ExecutionEngine/GenericValue.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Verifier.h"
#include "llvm/LinkAllPasses.h"
#include "llvm/MC/TargetRegistry.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/Host.h"
#include "llvm/Support/TargetParser.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Support/raw_os_ostream.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/Target/TargetOptions.h"

using namespace llvm;

class Stopwatch {
  private:
    std::chrono::high_resolution_clock::time_point startTime;
    bool isRunning;

  public:
    Stopwatch() : isRunning(false) {}

    void Start() {
        if (!isRunning) {
            startTime = std::chrono::high_resolution_clock::now();
            isRunning = true;
        }
    }

    void Stop() {
        if (isRunning) {
            isRunning = false;
        }
    }

    void Reset() { startTime = std::chrono::high_resolution_clock::now(); }

    std::chrono::milliseconds ElapsedMilliseconds() const {
        std::chrono::high_resolution_clock::time_point endTime;
        if (isRunning) {
            endTime = std::chrono::high_resolution_clock::now();
        } else {
            endTime = startTime;
        }

        return std::chrono::duration_cast<std::chrono::milliseconds>(endTime -
                                                                     startTime);
    }

    std::chrono::seconds ElapsedSeconds() const {
        return std::chrono::duration_cast<std::chrono::seconds>(
            ElapsedMilliseconds());
    }
};

std::string loadFile(const std::string &filename, bool binary) {
    std::string result;
    std::ifstream stream(filename,
                         std::ios::ate | (binary ? std::ios::binary
                                                 : std::ios_base::openmode(0)));

    if (!stream.is_open()) {
        return result;
    }

    result.reserve(stream.tellg());
    stream.seekg(0, std::ios::beg);

    result.assign((std::istreambuf_iterator<char>(stream)),
                  std::istreambuf_iterator<char>());
    return result;
}

static LLVMContext TheContext;
static IRBuilder<> Builder(TheContext);

constexpr size_t STATE_SIZE = 4096;

struct MLoop {
    Value *beforeValue;
    PHINode *startValue;
    Value *endValue;
    Value *afterValue;

    BasicBlock *beforeBlock;
    BasicBlock *startBlock;
    BasicBlock *endBlock;
    BasicBlock *afterBlock;
};

Function *make_function(Module &module, std::string_view code) {
    Type *void_type = Type::getVoidTy(TheContext);
    IntegerType *cell_type = IntegerType::get(TheContext, 8);
    IntegerType *index_type = IntegerType::get(TheContext, 32);
    PointerType *state_type = PointerType::get(cell_type, 0);
    Value *zero = ConstantInt::get(cell_type, 0);
    Value *one = ConstantInt::get(cell_type, 1);
    Value *minus_one = ConstantInt::get(cell_type, -1);
    FunctionType *getchar_type = FunctionType::get(cell_type, false);
    Function *getchar_func = Function::Create(
        getchar_type, Function::ExternalLinkage, "getchar", module);
    getchar_func->setCallingConv(CallingConv::C);
    FunctionType *putchar_type = FunctionType::get(void_type, cell_type, false);
    Function *putchar_func = Function::Create(
        putchar_type, Function::ExternalLinkage, "putchar", module);
    putchar_func->setCallingConv(CallingConv::C);

    FunctionType *main_type = FunctionType::get(void_type, false);
    Function *main =
        Function::Create(main_type, Function::ExternalLinkage, "main", module);
    main->setCallingConv(CallingConv::C);

    BasicBlock *main_block = BasicBlock::Create(TheContext, "code", main);
    IRBuilder<> builder(main_block);
    Value *state = builder.CreateAlloca(
        cell_type, ConstantInt::get(index_type, STATE_SIZE));
    Value *ptr = state;
    for (size_t i = 0; i < STATE_SIZE; i++) {
        builder.CreateStore(zero, ptr);
        ptr = builder.CreateGEP(cell_type, ptr, one);
    }

    std::stack<MLoop> loops;

    size_t code_index = 0;
    while (code_index < code.length()) {
        IRBuilder<> ir(main_block);
        char c = code[code_index];
        ++code_index;
        switch (c) {
        case '>':
            state = ir.CreateGEP(cell_type, state, one);
            break;
        case '<':
            state = ir.CreateGEP(cell_type, state, minus_one);
            break;
        case '+': {
            Value *v = ir.CreateLoad(cell_type, state);
            Value *r = ir.CreateAdd(v, one);
            ir.CreateStore(r, state);
            break;
        }
        case '-': {
            Value *v = ir.CreateLoad(cell_type, state);
            Value *r = ir.CreateSub(v, one);
            ir.CreateStore(r, state);
            break;
        }
        case '.': {
            Value *v = ir.CreateLoad(cell_type, state);
            ir.CreateCall(putchar_func, v);
            break;
        }
        case ',': {
            Value *ret = ir.CreateCall(getchar_func);
            ir.CreateStore(ret, state);
            break;
        }
        case '[': {
            MLoop loop;
            loop.beforeBlock = main_block;
            loop.startBlock = BasicBlock::Create(TheContext, "", main);
            loop.afterBlock = BasicBlock::Create(TheContext, "", main);
            loop.beforeValue = state;

            Value *v = ir.CreateLoad(cell_type, state);
            Value *cond = ir.CreateIsNotNull(v);
            ir.CreateCondBr(cond, loop.startBlock, loop.afterBlock);

            IRBuilder<> inner(loop.startBlock);
            loop.startValue = inner.CreatePHI(state_type, 0);
            loop.startValue->addIncoming(loop.beforeValue, loop.beforeBlock);

            loops.push(loop);
            main_block = loop.startBlock;
            state = loop.startValue;
            break;
        }
        case ']': {
            MLoop loop = loops.top();
            loops.pop();
            loop.endValue = state;
            loop.endBlock = main_block;

            Value *v = ir.CreateLoad(cell_type, state);
            Value *cond = ir.CreateIsNotNull(v);
            ir.CreateCondBr(cond, loop.startBlock, loop.afterBlock);

            loop.startValue->addIncoming(loop.endValue, loop.endBlock);

            main_block = loop.afterBlock;

            IRBuilder<> inner(main_block);
            PHINode *head_phi = inner.CreatePHI(state_type, 0);
            head_phi->addIncoming(loop.beforeValue, loop.beforeBlock);
            head_phi->addIncoming(loop.endValue, loop.endBlock);
            state = head_phi;
            break;
        }
        default:
            break;
        }
    }

    IRBuilder<> ir(main_block);
    ir.CreateRetVoid();

    return main;
}

// void run(std::string_view src) {
//     char *state = new char[4096]{};
//     char *ptr = state;
//     size_t src_index = 0;
//     std::stack<size_t> lp;
//     std::unordered_map<size_t, size_t> brackets;
//     for (size_t i = 0; i < src.length(); i++) {
//         if (src[i] == '[') {
//             lp.push(i);
//         } else if (src[i] == ']') {
//             if (lp.empty()) {
//                 printf("syntax error\n");
//                 return;
//             }
//             int l = lp.top();
//             lp.pop();
//             brackets[l] = i;
//             brackets[i] = l;
//         }
//     }

//     while (src_index < src.length()) {
//         char c = src[src_index];
//         ++src_index;
//         switch (c) {
//         case '>':
//             ++ptr;
//             break;
//         case '<':
//             --ptr;
//             break;
//         case '+':
//             ++*ptr;
//             break;
//         case '-':
//             --*ptr;
//             break;
//         case '.':
//             putchar(*ptr);
//             break;
//         case ',': {
//             int inp = getchar();
//             while (inp == '\n') {
//                 inp = getchar();
//             }
//             *ptr = inp;
//             if (*ptr == -1) {
//                 *ptr = 0;
//             }
//             break;
//         }
//         case '[':
//             if (*ptr == 0) {
//                 src_index = brackets[src_index - 1] + 1;
//             }
//             break;
//         case ']':
//             if (*ptr != 0) {
//                 src_index = brackets[src_index - 1];
//             }
//             break;
//         default:
//             break;
//         }
//     }
//     delete[] state;
// }

int main() {
    // const char *helloworld = "++++++++[>++++[>++>+++>+++>+<<<<-]>+>+>->>+[<]<-]"
    //                          ">>.>---.+++++++..+++.>>"
    //                          ".<-.<.+++.------.--------.>>+.>++.";
    // const char *cat = ",[.,]";
    auto mandelbrot = loadFile("mandelbrot.bf", true);
    std::string error;
    LLVMInitializeNativeAsmPrinter();
    LLVMInitializeNativeAsmParser();
    InitializeNativeTarget();
    InitializeAllTargetInfos();
    InitializeAllTargets();
    InitializeAllTargetMCs();
    InitializeAllAsmParsers();
    InitializeAllAsmPrinters();

    auto module = std::make_unique<Module>("bfcode", TheContext);

    auto m = module.get();
    auto f = make_function(*module, mandelbrot);
    verifyFunction(*f);
    // f->print(outs());
    // printf("; ----------------------------------------Optimized\n");
    // fflush(stdout);
    // auto engine = EngineBuilder(std::move(module))
    //                   .setEngineKind(llvm::EngineKind::JIT)
    //                   .create();
    // llvm::legacy::FunctionPassManager *fpm =
    //     new llvm::legacy::FunctionPassManager(m);
    // fpm->add(createVerifierPass());

    // fpm->add(createInstructionCombiningPass());
    // fpm->add(createLICMPass());
    // fpm->add(createIndVarSimplifyPass());
    // fpm->add(createLoopDeletionPass());

    // fpm->add(createGVNPass());
    // fpm->add(createSCCPPass());
    // fpm->add(createCFGSimplificationPass());
    // fpm->add(createInstructionCombiningPass());
    // fpm->add(createAggressiveDCEPass());
    // fpm->add(createCFGSimplificationPass());
    // fpm->add(createDeadStoreEliminationPass());

    // fpm->doInitialization();
    // fpm->run(*f);
    // engine->finalizeObject();
    // f->print(outs());

    std::string target_triple = llvm::sys::getDefaultTargetTriple();
    std::cout << target_triple << '\n';
    std::string err;
    const llvm::Target *target =
        llvm::TargetRegistry::lookupTarget(target_triple, err);
    if (!target) {
        return 1;
    }
    TargetOptions opt;
    TargetMachine *TheTargetMachine = target->createTargetMachine(
        target_triple, "generic", "", opt, Optional<Reloc::Model>());
    m->setTargetTriple(target_triple);
    m->setDataLayout(TheTargetMachine->createDataLayout());
    std::string output = "output.o";
    std::error_code err_code;
    raw_fd_ostream dest(output, err_code, sys::fs::OpenFlags::OF_None);
    if (err_code) {
        return 1;
    }

    llvm::legacy::PassManager pass;
    pass.add(createVerifierPass());
    pass.add(createInstructionCombiningPass());
    pass.add(createLICMPass());
    pass.add(createIndVarSimplifyPass());
    pass.add(createLoopDeletionPass());
    pass.add(createGVNPass());
    pass.add(createSCCPPass());
    pass.add(createCFGSimplificationPass());
    pass.add(createInstructionCombiningPass());
    pass.add(createAggressiveDCEPass());
    pass.add(createCFGSimplificationPass());
    pass.add(createDeadStoreEliminationPass());
    if (TheTargetMachine->addPassesToEmitFile(
            pass, dest, nullptr, CodeGenFileType::CGFT_ObjectFile)) {
        return 1;
    }
    pass.run(*m);
    dest.flush();

    // Stopwatch sw;
    // sw.Start();
    // engine->runFunction(f, {});
    // std::cout << sw.ElapsedMilliseconds() << '\n';
    // sw.Reset();
    // run(mandelbrot);
    // std::cout << sw.ElapsedMilliseconds() << '\n';
    return 0;
}