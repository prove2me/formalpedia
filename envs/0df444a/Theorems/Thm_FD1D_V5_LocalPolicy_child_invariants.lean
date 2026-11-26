-- Prove2me | Theorems.Thm_FD1D_V5_LocalPolicy_child_invariants
-- name    : FD1D.V5.LocalPolicy.child_invariants
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:22:06.885209+00:00
-- url     : https://prove2.me/theorems/a383d32c-9917-4f7e-8f16-11edbe1a3424
-- title:
--   Local Policy: child invariants
-- statement:
--   The Local Policy construction uses the child invariants property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/LocalInvariants.lean#L309-L346
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/LocalInvariants.lean#L309-L346

import Definitions.Def_FD1D_V5_LocalPolicy
import Definitions.Def_FD1D_V5_LocalInvariants
set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.LocalPolicy
noncomputable section

theorem FD1D.V5.LocalPolicy.child_invariants
    {a p h : ℝ} {x y : ℕ}
    (ha : 0 < a) (hp : 0 < p) (hh : 0 < h)
    (ht : discrepancy a p h x y ≤ h / 2) :
    discrepancyLeft a p h x y ≤ rateLeft a p h x y / 2 ∧
      regularizedMassLeft a p x y ≤ rateLeft a p h x y ∧
      discrepancyRight a p h x y ≤ rateRight a p h x y / 2 ∧
      regularizedMassRight a p x y ≤ rateRight a p h x y := by sorry
