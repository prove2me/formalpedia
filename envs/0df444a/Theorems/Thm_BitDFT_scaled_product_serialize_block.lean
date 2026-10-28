-- Prove2me | Theorems.Thm_BitDFT_scaled_product_serialize_block
-- name    : BitDFT.scaled_product_serialize_block
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T23:04:48.09303+00:00
-- url     : https://prove2.me/theorems/c24f2356-1acb-4f42-bed2-90eaddfd9235
-- title:
--   Serialize one scaled product at the requested shorter width
-- statement:
--   Let a coordinate magnitude a satisfy a≤2^q, and let n be the transform length with lg(n)+1≤q and n≤2^lg(n). The q-bit multiplier result, with its high-bit boundary correction, is the exact 2q-bit word consisting of 2q−w leading zeroes followed by the exact w-bit encoding of na, where w=q+lg(n)+1. If a binary descriptor has value w−1, the counted-block copier starts just after that zero prefix and writes precisely the shorter w-bit product word. It halts within 6w+4|descriptor|+2 transitions, preserving the source frame and restoring the descriptor tapes.
-- source:
--   Composition of the accepted scalar-product encoding theorem and counted-block tape routine for the single-coordinate stage of output rescaling.

import Definitions.Def_BitDFT_CountedBlock
import Theorems.Thm_BitDFT_counted_block_correct
import Theorems.Thm_BitDFT_scalar_scaled_word_complete_v2
set_option autoImplicit false
open IntMul

theorem BitDFT.scaled_product_serialize_block (q n a : ℕ) (hq : lg n + 1 ≤ q)
    (hn : n ≤ 2^(lg n)) (ha : a ≤ 2^q)
    (out descriptor : List Bool)
    (hdescWidth : val descriptor + 1 = q + lg n + 1) :
    let w := q + lg n + 1
    let z := if a.testBit q then n * 2^q else n * (a % 2^q)
    ∃ t : ℕ, t ≤ 6*w + 4*descriptor.length + 2 ∧
      IntMul.CountedStream.machine.step^[t]
        (BitDFT.CountedBlock.frame (List.replicate (2*q-w) false) out
          (bin w z) descriptor descriptor.reverse 0 .emit) =
        BitDFT.CountedBlock.frame (List.replicate (2*q-w) false) out
          (bin w z) descriptor descriptor.reverse (val descriptor+1) .halt ∧
      bin (2*q) (n*a) = List.replicate (2*q-w) false ++ bin w (n*a) := by sorry
