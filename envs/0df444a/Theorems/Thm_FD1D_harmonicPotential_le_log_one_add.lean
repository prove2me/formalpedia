-- Prove2me | Theorems.Thm_FD1D_harmonicPotential_le_log_one_add
-- name    : FD1D.harmonicPotential_le_log_one_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:02:38.825811+00:00
-- url     : https://prove2.me/theorems/11ffe40f-0241-521a-b88c-94df6f0eabf1
-- title:
--   FD1 D: harmonic Potential le log one add
-- statement:
--   The shifted harmonic sum is bounded by its integral:
--   `sum_{j=1}^k 1 / (a+j) ≤ log (1+k/a)`.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/PotentialBounds.lean#L26-L66
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/PotentialBounds.lean#L26-L66

import Definitions.Def_FD1D_Potential
import Definitions.Def_FD1D_Parameters
import Definitions.Def_FD1D_PotentialBounds
set_option autoImplicit true
open FD1D
noncomputable section
open Set intervalIntegral
open scoped BigOperators

theorem FD1D.harmonicPotential_le_log_one_add {a : ℝ} (ha : 0 < a) (k : ℕ) :
    harmonicPotential a k ≤ Real.log (1 + (k : ℝ) / a) := by sorry
