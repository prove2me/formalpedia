-- Prove2me | Theorems.Thm_FD1D_hazard_energy_bound_of_root
-- name    : FD1D.hazard_energy_bound_of_root
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:50:07.164742+00:00
-- url     : https://prove2.me/theorems/9e6dcb3a-e63a-5fc7-bfe1-b0ec1d2a474a
-- title:
--   FD1 D: hazard energy bound of root
-- statement:
--   Equation (2) with `H₀ = m⁻²`.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Tree.lean#L503-L515
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Tree.lean#L503-L515

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Tree
set_option autoImplicit true
open FD1D
noncomputable section

theorem FD1D.hazard_energy_bound_of_root
    (L : ℕ) {a m : ℝ} (h b : ∀ d, DyadicNode d → ℝ)
    (hm : m ≠ 0) (hroot : h 0 dyadicRoot = 1 / m)
    (hlocal : ∀ d, d < L → ∀ v,
      (b d v) ^ 2 ≤ 2 * a ^ 2 *
        (childAverage (fun d v => (h d v) ^ 2) d v - (h d v) ^ 2)) :
    internalWeightedSum (fun d v => (b d v) ^ 2) L ≤
      2 * a ^ 2 * (hazardEnergy h L - 1 / m ^ 2) := by sorry
