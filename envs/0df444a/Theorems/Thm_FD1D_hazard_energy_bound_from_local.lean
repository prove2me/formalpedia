-- Prove2me | Theorems.Thm_FD1D_hazard_energy_bound_from_local
-- name    : FD1D.hazard_energy_bound_from_local
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:50:05.934571+00:00
-- url     : https://prove2.me/theorems/f6b18e24-9776-5c7a-a9e0-6c045e1b9462
-- title:
--   FD1 D: hazard energy bound from local
-- statement:
--   Equation (2) directly from equation (1), with the latter stated in its
--   displayed divided form.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Tree.lean#L489-L500
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Tree.lean#L489-L500

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Tree
set_option autoImplicit true
open FD1D
noncomputable section

theorem FD1D.hazard_energy_bound_from_local
    (L : ℕ) {a : ℝ}
    (h b : ∀ d, DyadicNode d → ℝ) (ha : a ≠ 0)
    (hlocal : ∀ d, d < L → ∀ v,
      (b d v) ^ 2 / (2 * a ^ 2) ≤
        childAverage (fun d v => (h d v) ^ 2) d v - (h d v) ^ 2) :
    internalWeightedSum (fun d v => (b d v) ^ 2) L ≤
      2 * a ^ 2 * (hazardEnergy h L - hazardEnergy h 0) := by sorry
