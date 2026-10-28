-- Prove2me | Theorems.Thm_BitDFT_binary_counter_add_bounded
-- name    : BitDFT.binary_counter_add_bounded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T15:34:46.814286+00:00
-- url     : https://prove2.me/theorems/b14304a5-09ee-40f9-b2d7-b0924a1c2431
-- title:
--   Unary-controlled binary addition has linear runtime and bounded output length
-- statement:
--   For any little-endian binary word w and unary count K, the explicit finite counter halts within 5K+2|w|+1 transitions with a word v of value value(w)+K and length at most |w|+K. It clears the unary count, returns the binary head to cell one, and preserves native input/output caller data. The full final configuration is specified. The length guarantee supports the subsequent linear-time serialization of the computed Fourier precision.
-- source:
--   Strengthens the accepted BitDFT.binary_counter_add contract with an output-size guarantee needed for header serialization. It uses the identical machine and exact execution proof, plus induction showing that one increment grows the binary word by at most one bit.

import Definitions.Def_BitDFT_BinaryCounter
open BitDFT.BinaryCounter IntMul

theorem BitDFT.binary_counter_add_bounded (base : machine.Cfg) (w : List Bool) (k : ℕ) :
    ∃ t v, t ≤ 5*k+2*w.length+1 ∧ value v = value w+k ∧ v.length ≤ w.length+k ∧
      machine.step^[t] (frame base .tick w k 1) = frame base .halt v 0 1 := by sorry
