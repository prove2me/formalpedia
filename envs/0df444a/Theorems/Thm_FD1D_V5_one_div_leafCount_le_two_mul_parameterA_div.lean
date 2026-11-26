-- Prove2me | Theorems.Thm_FD1D_V5_one_div_leafCount_le_two_mul_parameterA_div
-- name    : FD1D.V5.one_div_leafCount_le_two_mul_parameterA_div
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:47:06.985497+00:00
-- url     : https://prove2.me/theorems/3805b813-ba06-4c17-a312-7d4bcd05fe45
-- title:
--   V5: one div leaf Count le two mul parameter A div
-- statement:
--   The spatial discretization estimate `1/n ≤ 2a/m`.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/Parameters.lean#L106-L112
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/Parameters.lean#L106-L112

import Definitions.Def_FD1D_Tree
import Definitions.Def_FD1D_V5_Parameters
set_option autoImplicit true
open FD1D FD1D.V5
noncomputable section
open Filter Asymptotics

theorem FD1D.V5.one_div_leafCount_le_two_mul_parameterA_div {m : ℕ}
    (hm : 1 ≤ m) :
    (1 : ℝ) / leafCount m ≤ 2 * parameterA m / m := by sorry
