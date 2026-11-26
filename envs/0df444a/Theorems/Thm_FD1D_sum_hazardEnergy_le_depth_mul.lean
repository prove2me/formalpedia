-- Prove2me | Theorems.Thm_FD1D_sum_hazardEnergy_le_depth_mul
-- name    : FD1D.sum_hazardEnergy_le_depth_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:56:45.00788+00:00
-- url     : https://prove2.me/theorems/092df254-9922-4c3f-97d4-7054064325b3
-- title:
--   FD1 D: sum hazard Energy le depth mul
-- statement:
--   A nondecreasing hazard energy gives `sum_{ell=1}^L H_ell ≤ L H_L`.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Potential.lean#L169-L181
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Potential.lean#L169-L181

import Definitions.Def_FD1D_Tree
import Definitions.Def_FD1D_Drift
import Definitions.Def_FD1D_Potential
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators

theorem FD1D.sum_hazardEnergy_le_depth_mul
    {L : ℕ} {h : ∀ d, DyadicNode d → ℝ}
    (hmono : Monotone (hazardEnergy h)) :
    (∑ d ∈ Finset.range L, hazardEnergy h (d + 1)) ≤
      (L : ℝ) * hazardEnergy h L := by sorry
