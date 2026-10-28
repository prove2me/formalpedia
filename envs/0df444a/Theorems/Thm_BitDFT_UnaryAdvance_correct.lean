-- Prove2me | Theorems.Thm_BitDFT_UnaryAdvance_correct
-- name    : BitDFT.UnaryAdvance.correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T23:31:14.960985+00:00
-- url     : https://prove2.me/theorems/1172755e-1902-4b54-bf20-2192384cb77a
-- title:
--   Advance a source head by a unary count in exact time
-- statement:
--   Let a separate counter tape contain exactly $L$ consecutive one symbols from its current head, followed by a non-one symbol. The unary-controlled positioning machine advances both the source and counter heads by $L$ cells, preserves all tape contents and other heads, and halts after exactly $L+1$ transitions. This gives an exact finite-machine bound for positioning the source head before processing a fixed-width output field.
-- source:
--   Exact run theorem for the unary head-positioning stage used by tape-level output serialization.

import Definitions.Def_BitDFT_UnaryAdvance
import Mathlib.Tactic
set_option autoImplicit false
open IntMul BitDFT.UnaryAdvance

theorem BitDFT.UnaryAdvance.correct (N : MultitapeTM) (source counter : Fin N.k)
    (hsc : source ≠ counter) (base : N.Cfg)
    (L sourceHead counterHead : ℕ)
    (hones : ∀ r, r < L → base.cells counter (counterHead+r) = N.one)
    (hstop : base.cells counter (counterHead+L) ≠ N.one) :
    (machine N source counter hsc).step^[L+1]
        (frame N source counter hsc base false sourceHead counterHead) =
      frame N source counter hsc base true (sourceHead+L) (counterHead+L) := by sorry
