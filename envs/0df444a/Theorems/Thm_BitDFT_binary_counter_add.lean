-- Prove2me | Theorems.Thm_BitDFT_binary_counter_add
-- name    : BitDFT.binary_counter_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T14:50:50.64797+00:00
-- url     : https://prove2.me/theorems/704c4f07-84ff-4415-9649-6f681848f0ff
-- title:
--   Unary-controlled binary addition runs in amortized linear multitape time
-- statement:
--   Let w be any little-endian binary word and K any natural number. Starting with w on work tape 2 and K unary marks on work tape 3, the explicit finite machine halts in at most 5K+2|w|+1 transitions with a binary word representing value(w)+K. Its unary tape is cleared, the binary head returns to cell one, and both native input/output tapes and their heads retain arbitrary caller data. The conclusion identifies the full final configuration. Leading zero padding is allowed, and zero counts and empty words are included.
-- source:
--   Exact phase invariants for the finite counter, followed by a potential argument counting one bits. This provides the arithmetic core of the precision rewrite; preparing the unary increment count and serializing the final precision header remain separate machine stages.

import Definitions.Def_BitDFT_BinaryCounter
open BitDFT.BinaryCounter IntMul

theorem BitDFT.binary_counter_add (base : machine.Cfg) (w : List Bool) (k : ℕ) :
    ∃ t v, t ≤ 5*k+2*w.length+1 ∧ value v = value w+k ∧
      machine.step^[t] (frame base .tick w k 1) = frame base .halt v 0 1 := by sorry
