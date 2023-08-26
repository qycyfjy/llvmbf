#include <fstream>
#include <iostream>
#include <stack>
#include <stdio.h>
#include <string_view>
#include <unordered_map>

std::string loadFile(const std::string &filename, bool binary) {
  std::string result;
  std::ifstream stream(
      filename,
      std::ios::ate | (binary ? std::ios::binary : std::ios_base::openmode(0)));

  if (!stream.is_open()) {
    return result;
  }

  result.reserve(stream.tellg());
  stream.seekg(0, std::ios::beg);

  result.assign((std::istreambuf_iterator<char>(stream)),
                std::istreambuf_iterator<char>());
  return result;
}

void run(std::string_view src) {
  char *state = new char[1024 * 1024 * 8]{};
  char *ptr = state;
  int src_index = 0;
  std::stack<int> lp;
  std::unordered_map<int, int> brackets;
  for (int i = 0; i < src.length(); i++) {
    if (src[i] == '[') {
      lp.push(i);
    } else if (src[i] == ']') {
      if (lp.empty()) {
        printf("syntax error\n");
        return;
      }
      int l = lp.top();
      lp.pop();
      brackets[l] = i;
      brackets[i] = l;
    }
  }

  while (src_index < src.length()) {
    char c = src[src_index];
    ++src_index;
    switch (c) {
    case '>':
      ++ptr;
      break;
    case '<':
      --ptr;
      break;
    case '+':
      ++*ptr;
      break;
    case '-':
      --*ptr;
      break;
    case '.':
      putchar(*ptr);
      break;
    case ',': {
      int inp = getchar();
      while (inp == '\n') {
        inp = getchar();
      }
      *ptr = inp;
      if (*ptr == -1) {
        *ptr = 0;
      }
      break;
    }
    case '[':
      if (*ptr == 0) {
        src_index = brackets[src_index - 1] + 1;
      }
      break;
    case ']':
      if (*ptr != 0) {
        src_index = brackets[src_index - 1];
      }
      break;
    default:
      break;
    }
  }
  delete[] state;
}

int main() {
  const char *helloworld =
      "++++++++[>++++[>++>+++>+++>+<<<<-]>+>+>->>+[<]<-]>>.>---.+++++++..+++.>>"
      ".<-.<.+++.------.--------.>>+.>++.";
  run(helloworld);
  run(",[>,]<[<]>[.>]");
  printf("\n");
  auto mandelbrot = loadFile("mandelbrot.bf", true);
  run(mandelbrot);
  return 0;
}