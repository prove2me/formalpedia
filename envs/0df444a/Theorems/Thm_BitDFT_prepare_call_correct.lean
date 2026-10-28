-- Prove2me | Theorems.Thm_BitDFT_prepare_call_correct
-- name    : BitDFT.prepare_call_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T17:21:05.531821+00:00
-- url     : https://prove2.me/theorems/41e2be77-8a2d-410d-93a2-711c272bc07a
-- title:
--   Prepare a Fourier child-call buffer from native input with all transitions charged
-- statement:
--   Let n,b be positive, q=b+3 lg(n)+5, and w the rewritten Fourier input. For any target alphabet and r reserved child banks, the composed machine starts from the ordinary encoded request and reaches its exact final configuration within 27nq+3|w|+6 transitions. The output tape is a blank gap followed by w and a separator, with its head at cell 1. All r reserved child banks are still blank and their heads are still at zero. The bound includes the actual stage-handoff transition.
-- source:
--   Native-to-mutable-buffer composition for the full transfer theorem. Child-bank head positioning, actual child execution, output scaling, and the normalized Fourier machine remain separate obligations.

import Definitions.Def_BitDFT_PrepareCall
open BitDFT.PrepareCall BitDFT IntMul MachineSequence

theorem BitDFT.prepare_call_correct (N : MultitapeTM) (r n b : ℕ) (hn : 1 ≤ n) (hb : 1 ≤ b) (U : Fin n → ℤ × ℤ) :
    let q := guardPrecision n b
    let w := fourierInput q U
    ∃ t v, t ≤ 27*n*q+3*w.length+6 ∧
      (machine N r).step^[t] ((machine N r).initCfg (requestedInput b U) []) =
        final N r (RewriteInput.final n b (encVector (q+1) U) v) w ∧
      (final N r (RewriteInput.final n b (encVector (q+1) U) v) w).cells (machine N r).outTape =
        (machine N r).tapeOf ([(machine N r).blank]++w.map (machine N r).bitSym++[(machine N r).sep]) ∧
      (final N r (RewriteInput.final n b (encVector (q+1) U) v) w).head (machine N r).outTape = 1 ∧
      (∀ i : Fin (machine N r).k, 2 ≤ i.val → i.val < r+2 →
        (final N r (RewriteInput.final n b (encVector (q+1) U) v) w).cells i = N.tapeOf [] ∧
        (final N r (RewriteInput.final n b (encVector (q+1) U) v) w).head i = 0) := by sorry
