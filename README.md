# ♟️ Chessboard Traversal-Based Lightweight Key Generator for IoT Systems

A novel lightweight cryptographic key generation scheme for resource-constrained IoT devices based on dynamic chessboard traversal and hash-guided movement selection.

## 📖 Overview

Traditional key scheduling algorithms often introduce significant computational overhead or exhibit predictable structures that weaken security in constrained environments. This project proposes a lightweight key generation mechanism that combines cryptographic hashing with adaptive chessboard traversal to generate highly diffused and unpredictable round keys.

The scheme dynamically selects between custom chess-piece movement patterns (Zebra and Camel) and generates round keys through nonlinear traversal paths on a virtual chessboard.

## ✨ Key Features

* Lightweight design suitable for IoT devices
* Dynamic chessboard traversal-based key generation
* Hash-guided movement selection
* Nonlinear round key derivation
* Strong avalanche behavior
* Low inter-round correlation
* Resource-efficient implementation
* Raspberry Pi Pico deployment

## 🏗️ System Architecture

Input Parameters:

* Secret Key (K)
* Nonce (N)
* Number of Rounds (R)
* Walks per Round (W)
* Chessboard Size (c × c)

### Traversal Pieces

#### Zebra Piece

Movement Pattern:

(±3, ±2), (±2, ±3)

#### Camel Piece

Movement Pattern:

(±3, ±1), (±1, ±3)

The active chess piece is selected dynamically using cryptographic hash outputs during each traversal step.

## ⚙️ Algorithm Workflow

### Stage 1: Initialization

1. Generate seed using:

seed = H(K || N)

2. Compute starting square:

startsq = seed mod (c × c)

### Stage 2: Dynamic Traversal

For each round:

* Compute hash values h1 and h2
* Select Zebra or Camel piece
* Generate legal moves
* Select next square using hash-guided indexing
* Build traversal sequence

### Stage 3: Round Key Generation

After completing the walk sequence:

RK[r] = MSB(H(K || N || r || walk))

Round keys are generated independently for every round.

## 🔬 Experimental Evaluation

### Hardware Platform

* Raspberry Pi Pico
* RP2040 Dual-Core ARM Cortex-M0+
* 133 MHz Processor
* MicroPython/Python Implementation

### Performance Metrics

| Metric         | Result     |
| -------------- | ---------- |
| Execution Time | 11.73 ms   |
| Peak RAM Usage | 23.6 KB    |
| Flash Size     | 13.8 KB    |
| CPU Cycles     | 1.56 × 10⁶ |

### Security Analysis

#### Key Sensitivity

* Average Changed Bits: 1023.70
* Ideal Avalanche: 1024

#### Nonce Sensitivity

* Average Changed Bits: 1023.77
* Ideal Avalanche: 1024

#### Round Sensitivity

* Average Changed Bits: 63.95
* Ideal Avalanche: 64

#### Statistical Analysis

* NIST Monobit Pass Rate: 98.7%
* Average Proportion of Ones: 0.4998
* Average Correlation Coefficient: 0.00065

## 📂 Project Structure

```text
.
├── key_generator.py
├── traversal_engine.py
├── chess_pieces.py
├── sensitivity_tests.py
├── statistical_tests.py
├── benchmark.py
├── requirements.txt
└── README.md
```

## 🛠️ Technologies Used

* Python
* MicroPython
* hashlib
* Raspberry Pi Pico
* RP2040
* IoT Security
* Cryptographic Hash Functions

## 📊 Applications

* Lightweight Encryption Systems
* Session Key Generation
* IoT Authentication Protocols
* Secure Device Communication
* Embedded Security Solutions
* Resource-Constrained Cryptographic Systems

## 🚀 Future Enhancements

* Integration with lightweight block ciphers
* Additional chess-piece movement models
* FPGA implementation
* Hardware security module support
* AI-assisted cryptographic randomness analysis
* Formal cryptographic security proofs

## 📄 Research Paper

**Chessboard Traversal-Based Lightweight Key Generator for IoT Systems**

Authors:

* Pranav Thobhani
* Jay Dave
* Sameera Muhamed Salam

Department of Computer Science
BITS Pilani Hyderabad Campus

## 📜 License

This project is intended for academic research and educational purposes.
