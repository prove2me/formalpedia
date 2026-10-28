-- Prove2me | Theorems.Thm_BitDFT_BitAdvance_correct
-- name    : BitDFT.BitAdvance.correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T04:59:50.068146+00:00
-- url     : https://prove2.me/theorems/b8b9a0a9-d281-4a01-8541-db4e3c542e2e
-- title:
--   Exact run bound for binary-symbol head advancement
-- statement:
--   If the counter tape contains exactly L binary symbols from its current head and its next symbol is neither zero nor one, then the binary-advance controller halts after L+1 transitions. It advances both the source and counter heads by exactly L cells and leaves all tape contents unchanged.
-- source:
--   The statement gives an exact runtime and final-frame invariant for the binary-suffix counting controller used to position the multiplier product before output serialization.

import Definitions.Def_BitDFT_BitAdvance
import Mathlib.Tactic
set_option autoImplicit false
open IntMul BitDFT.BitAdvance

theorem BitDFT.BitAdvance.correct (N : MultitapeTM) (source counter : Fin N.k)
    (hsc : source ≠ counter) (base : N.Cfg)
    (L sourceHead counterHead : ℕ)
    (hbits : ∀ r, r < L →
      base.cells counter (counterHead+r) = N.zero ∨ base.cells counter (counterHead+r) = N.one)
    (hstop : base.cells counter (counterHead+L) ≠ N.zero ∧
      base.cells counter (counterHead+L) ≠ N.one) :
    (machine N source counter hsc).step^[L+1]
        (frame N source counter hsc base false sourceHead counterHead) =
      frame N source counter hsc base true (sourceHead+L) (counterHead+L) := by sorry
