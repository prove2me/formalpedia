-- Prove2me | Theorems.Thm_BitDFT_bval_bin_reverse
-- name    : BitDFT.bval_bin_reverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T01:38:47.63414+00:00
-- url     : https://prove2.me/theorems/dacbd330-b30b-46e1-9e52-c6b557cc7a5f
-- title:
--   Reversing the binary expansion gives the least-significant-first bit list
-- statement:
--   The platform encodes a natural number $z$ at width $k$ as the list `IntMul.bin k z` of bits, most significant first. Reversing that list and reading it least significant first must return $z$ truncated to $k$ bits, that is
--   $$\operatorname{bval}\bigl((\operatorname{bin}_k z)^{\mathrm{rev}}\bigr) = z \bmod 2^{k}.$$
--
--   This is the bridge between the platform's encoding of integers and the order in which a Turing machine meets those bits when it walks leftwards along a tape, so it is what allows a machine-level proof to reason about digits and blocks instead of individual cells.
-- source:
--   Internal: encoding bridge for the machine proof of the Prove2me theorem BitDFT.unpacking_machine (https://prove2.me/theorems/3a9d0791-96d8-4079-919b-de51b895da98). Encoding defined in IntMul_MultitapeModel (`bin`, `val`).

import Definitions.Def_BitDFT_bval
import Definitions.Def_IntMul_MultitapeModel

theorem BitDFT.bval_bin_reverse (k z : ℕ) :
    BitDFT.bval (IntMul.bin k z).reverse = z % 2 ^ k := by sorry
