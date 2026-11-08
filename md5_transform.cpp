#include <iostream>
#include <cmath>
#include <vector>
#include <map>
#include <utility>
#include <functional>
#include <string>
#include <cstdint>
#include <bitset>
#include <chrono>

typedef long long ll;

class MD5 {
private:
    std::string s = "";
    std::vector<uint8_t> v;
    uint64_t orig_size;
    std::string res;

    std::vector<uint32_t> defaults = {0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476};

    uint32_t A = 0x67452301;
    uint32_t B = 0xEFCDAB89;
    uint32_t C = 0x98BADCFE;
    uint32_t D = 0x10325476;

    uint32_t a;
    uint32_t b;
    uint32_t c;
    uint32_t d;

    std::vector<uint32_t> Ks;
    std::vector<uint32_t> shifts;

    void convert_to_bytes() {
        std::vector<uint8_t> byte_v(reinterpret_cast<const uint8_t*>(s.data()), reinterpret_cast<const uint8_t*>(s.data()+s.size()));
        v = byte_v;
    }
    void padding() {
        orig_size = v.size();
        v.push_back(0x80);
        while (v.size() % 64 != 56) {
            v.push_back(0x00);
        }
        uint64_t orig_size_bytes = orig_size * 8;
        for (int i = 0; i < 8; i++) {
            v.push_back((orig_size_bytes >> (8*i)) & 0xFF);
        }
    }
     static uint32_t bytes_to_word(uint8_t x, uint8_t y, uint8_t z, uint8_t w) {
        uint32_t t = (static_cast<uint32_t>(w) << 24) | (static_cast<uint32_t>(z) << 16) | (static_cast<uint32_t>(y) << 8) | static_cast<uint32_t>(x);
        return t;
    }
    std::vector<uint32_t> form_words() const {
        std::vector<uint32_t> blocks;
        for (int i = 0; i < v.size(); i += 4) {
            blocks.push_back(bytes_to_word(v[i], v[i+1], v[i+2], v[i+3]));
        }
        return blocks;
    }
    void set_defaults() {
        A = defaults[0];
        B = defaults[1];
        C = defaults[2];
        D = defaults[3];

        a = defaults[0];
        b = defaults[1];
        c = defaults[2];
        d = defaults[3];
    }

    static uint32_t F(uint32_t x, uint32_t y, uint32_t z) {
        return ((x & y) | (z & (~x)));
    }
    static uint32_t G(uint32_t x, uint32_t y, uint32_t z) {
        return ((x & z) | (y & (~z)));
    }
    static uint32_t H(uint32_t x, uint32_t y, uint32_t z) {
        return (x ^ y ^ z);
    }
    static uint32_t I(uint32_t x, uint32_t y, uint32_t z) {
        return (y ^ (x | (~z)));
    }
    uint32_t rotate_left(uint32_t x, unsigned shift) {
        if (shift >= 32) {
            shift %= 32;
        }
        if (shift == 0) {
            return x;
        }
        uint32_t tail = (x >> (32 - shift));
        return ((x << shift) | tail);
    }
    void fill_Ks() {
        for (ll i = 0; i < 64; i++) {
            Ks.push_back(std::floor(std::pow(2,32) * std::abs(std::sin(i + 1))));
        }
    }
    void fill_shifts() {
        for (int i = 0; i < 64; i++) {
            if (i <= 15) {
                shifts.push_back(7 + (i % 4) * 5);
            } else if (i <= 31) {
                if (i % 4 == 0) {
                    shifts.push_back(5);
                } else if (i % 4 == 1) {
                    shifts.push_back(9);
                } else if (i % 4 == 2) {
                    shifts.push_back(14);
                } else {
                    shifts.push_back(20);
                }
            } else if (i <= 47) {
                if (i % 4 == 0) {
                    shifts.push_back(4);
                } else if (i % 4 == 1) {
                    shifts.push_back(11);
                } else if (i % 4 == 2) {
                    shifts.push_back(16);
                } else {
                    shifts.push_back(23);
                }
            } else {
                if (i % 4 == 0) {
                    shifts.push_back(6);
                } else if (i % 4 == 1) {
                    shifts.push_back(10);
                } else if (i % 4 == 2) {
                    shifts.push_back(15);
                } else {
                    shifts.push_back(21);
                }
            }
        }
    }

    std::map<int, std::function<size_t(int)>> word_index {
        {1,[](int i) {
            return i;
        }},
        {2,[](int i) {
            return (5*i+1) % 16;
        }},
        {3,[](int i) {
            return (3*i+5) % 16;
        }},
        {4, [](int i) {
            return (7*i) % 16;
        }}
    };
    std::pair<uint32_t, size_t> one_step(int i) {
        if (i <= 15) {
            return {F(b,c,d),word_index[1](i)};
        } else if (i <= 31) {
            return {G(b,c,d),word_index[2](i)};
        } else if (i <= 47) {
            return {H(b,c,d),word_index[3](i)};
        } else {
            return {I(b,c,d),word_index[4](i)};
        }
    }
    void hashing() {
        std::vector<uint32_t> blocks = form_words();
        for (int u = 0; u < blocks.size(); u += 16) {
            a = A;
            b = B;
            c = C;
            d = D;
            for (int i = 0; i < 64; i++) {
                uint32_t new_value = b + rotate_left(a + one_step(i).first + Ks[i] + blocks[one_step(i).second + u], shifts[i]);
                a = d;
                d = c;
                c = b;
                b = new_value;
            }
            A += a;
            B += b;
            C += c;
            D += d;
        }
    }

    static char hex_symb(uint8_t b) {
        std::map<uint8_t, char> conv = {
            {0,'0'},
            {1,'1'},
            {2,'2'},
            {3,'3'},
            {4,'4'},
            {5,'5'},
            {6,'6'},
            {7,'7'},
            {8,'8'},
            {9,'9'},
            {10,'a'},
            {11,'b'},
            {12,'c'},
            {13,'d'},
            {14,'e'},
            {15,'f'}
        };
        return conv[b];
    }

    void process_one_register(uint32_t reg, std::vector<uint8_t>& vec) {
        for (int i = 0; i <= 24; i += 8) {
            vec.push_back((reg >> i) & 0xFF);
        }
    }
    
    std::string get_digest() {
        std::vector<uint8_t> vec;
        process_one_register(A, vec);
        process_one_register(B, vec);
        process_one_register(C, vec);
        process_one_register(D, vec);
        std::string res = "";
        for (auto byte : vec) {
            uint8_t fst = (byte >> 4);
            uint8_t sec = (byte & 0x0F);
            res += hex_symb(fst);
            res += hex_symb(sec);
        }
        return res;
    }
public:
    MD5(std::string str):
    s(str) {
        set_string(str);
        fill_Ks();
        fill_shifts();
    }
    void set_string(std::string raw_s) {
        set_defaults();
        s = raw_s;
        res = s;
        this->convert_to_bytes();
        this->padding();
        fill_Ks();
        fill_shifts();
        hashing();
        std::cout << "Setted successfully" << std::endl;
    }
    std::string get_hash() {
        return get_digest();
    }
    std::string get_string() const {
        return s;
    }
};

int main() {
    auto start = std::chrono::steady_clock::now();
    MD5 md5("");
    md5.set_string("I came, I saw, I conquered");
    std::cout << "-> String: " << md5.get_string() << std::endl;
    std::cout << "-> Hash: " << md5.get_hash() << std::endl;
    auto end = std::chrono::steady_clock::now();
    std::cout << "-> Time consumed (ms): " << std::chrono::duration_cast<std::chrono::microseconds>(end - start).count() << std::endl;
    std::cout << "-> Time consumed (sec): " << std::chrono::duration_cast<std::chrono::microseconds>(end - start).count() / 1000000.0 << std::endl;
    return 0;
}