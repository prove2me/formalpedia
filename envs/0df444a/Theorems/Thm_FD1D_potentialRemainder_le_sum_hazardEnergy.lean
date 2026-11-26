-- Prove2me | Theorems.Thm_FD1D_potentialRemainder_le_sum_hazardEnergy
-- name    : FD1D.potentialRemainder_le_sum_hazardEnergy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:56:21.0153+00:00
-- url     : https://prove2.me/theorems/535adb43-df99-4bc8-ad3d-b88999eed1a0
-- title:
--   FD1 D: potential Remainder le sum hazard Energy
-- statement:
--   `R ≤ sum_{ell=1}^L H_ell`.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Potential.lean#L148-L166
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Potential.lean#L148-L166

import Definitions.Def_FD1D_Tree
import Definitions.Def_FD1D_Drift
import Definitions.Def_FD1D_Potential
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators

theorem FD1D.potentialRemainder_le_sum_hazardEnergy
    {L : ℕ} {a : ℝ} {N : ∀ d, DyadicNode d → ℕ}
    {q h : ∀ d, DyadicNode d → ℝ}
    (ha : 0 < a)
    (hq0 : ∀ d v, 0 ≤ q d v)
    (hq1 : ∀ d v, q d v ≤ 1)
    (hmajor : ∀ d v,
      nodeMass d v ≤ ((N d v : ℝ) + a) * h d v) :
    potentialRemainder L a N q ≤
      ∑ d ∈ Finset.range L, hazardEnergy h (d + 1) := by sorry
