-- Prove2me | Theorems.Thm_BitDFT_bval_chunk
-- name    : BitDFT.bval_chunk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T01:38:46.964566+00:00
-- url     : https://prove2.me/theorems/b59db020-bbcf-4305-841b-f56b523f751f
-- title:
--   Blocks of a least-significant-first bit list are its base-$2^k$ digits
-- statement:
--   Read a finite list of bits least significant first and let $v$ be the number it denotes. For every block width $k$ and every block index $i$, the block of $k$ bits that starts at position $ik$ denotes exactly
--   $$v \operatorname{div} 2^{ik} \bmod 2^{k}.$$
--
--   In other words the blocks of the list are the base-$2^k$ digits of $v$, lowest first. This is the step that turns a tape containing the binary expansion of an integer into the sequence of base-$2^k$ digits a digit-extraction machine has to emit, and it is the companion of `BitDFT.bval_bin_reverse`.
-- source:
--   Internal: block extraction for the machine proof of the Prove2me theorem BitDFT.unpacking_machine (https://prove2.me/theorems/3a9d0791-96d8-4079-919b-de51b895da98).

import Definitions.Def_BitDFT_bval

theorem BitDFT.bval_chunk (l : List Bool) (k i : ℕ) :
    BitDFT.bval ((l.drop (i * k)).take k) = BitDFT.bval l / 2 ^ (i * k) % 2 ^ k := by sorry
