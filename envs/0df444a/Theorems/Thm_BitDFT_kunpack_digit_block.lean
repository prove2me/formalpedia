-- Prove2me | Theorems.Thm_BitDFT_kunpack_digit_block
-- name    : BitDFT.kunpack_digit_block
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-02T21:44:40.357607+00:00
-- url     : https://prove2.me/theorems/ad6239c4-cd3b-4829-b251-d205196ab5b5
-- title:
--   Base-$2^\beta$ digit of an integer is a bit block of its residue
-- statement:
--   Let $B = 2^\beta$ and let $d_i$ be the $i$-th base-$B$ digit of an integer $W$, that is $d_i = \lfloor W/B^i \rfloor \bmod B \in [0,B)$. Write $X = W \bmod B^r$, the residue of $W$ in $[0,B^r)$ — the two's-complement bit pattern of $W$ truncated to $\beta r$ bits. For every $i < r$, the digit $d_i$ is exactly the block of $\beta$ consecutive bits of $X$ starting at bit position $\beta i$, read least significant bit first. This is the bit-level reading of the base-$B$ expansion that a machine extracting Kronecker-substitution digits has to implement: it says that the $i$-th digit can be produced by scanning the residue, and it is what lets the balanced-digit extraction of `IntMul.HvdH.kunpack` be driven from the binary encoding of $W$.
-- source:
--   Internal: bit-level correctness of the digit extraction for the Prove2me theorem BitDFT.unpacking_machine (https://prove2.me/theorems/3a9d0791-96d8-4079-919b-de51b895da98). Statement of the identity needed to pass from IntMul.HvdH.kunpack (base-2^beta, balanced digits) to the binary tape contents of the packed integer.

import Mathlib

theorem BitDFT.kunpack_digit_block (β r : ℕ) (W : ℤ) (i : ℕ) (hi : i < r) :
    ((W / (2 : ℤ) ^ (β * i)) % (2 : ℤ) ^ β).toNat
      = (W % (2 : ℤ) ^ (β * r)).toNat / 2 ^ (β * i) % 2 ^ β := by sorry
