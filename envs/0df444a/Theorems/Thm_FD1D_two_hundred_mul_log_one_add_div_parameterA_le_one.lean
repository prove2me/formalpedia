-- Prove2me | Theorems.Thm_FD1D_two_hundred_mul_log_one_add_div_parameterA_le_one
-- name    : FD1D.two_hundred_mul_log_one_add_div_parameterA_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:24:18.671923+00:00
-- url     : https://prove2.me/theorems/5c44d063-26a6-450e-8c45-f9982fdcde75
-- title:
--   FD1 D: two hundred mul log one add div parameter A le one
-- statement:
--   Divided form of the logarithmic budget appearing in Section 5.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/PotentialBounds.lean#L188-L194
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/PotentialBounds.lean#L188-L194

import Definitions.Def_FD1D_Potential
import Definitions.Def_FD1D_Parameters
import Definitions.Def_FD1D_PotentialBounds
set_option autoImplicit true
open FD1D
noncomputable section
open Set intervalIntegral
open scoped BigOperators

theorem FD1D.two_hundred_mul_log_one_add_div_parameterA_le_one
    {m : ℕ} (hm : 1 ≤ m) :
    200 * Real.log
        (1 + (m : ℝ) / (parameterA m : ℝ)) /
        (parameterA m : ℝ) ≤ 1 := by sorry
