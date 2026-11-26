-- Prove2me | Theorems.Thm_FD1D_two_hundred_mul_log_one_add_le_parameterA
-- name    : FD1D.two_hundred_mul_log_one_add_le_parameterA
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:03:16.870247+00:00
-- url     : https://prove2.me/theorems/acfc4b2a-4c91-5500-9167-cbbe155fbdfd
-- title:
--   FD1 D: two hundred mul log one add le parameter A
-- statement:
--   The chosen parameter dominates `200 * log (1 + m/a)`.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/PotentialBounds.lean#L140-L185
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/PotentialBounds.lean#L140-L185

import Definitions.Def_FD1D_Potential
import Definitions.Def_FD1D_Parameters
import Definitions.Def_FD1D_PotentialBounds
set_option autoImplicit true
open FD1D
noncomputable section
open Set intervalIntegral
open scoped BigOperators

theorem FD1D.two_hundred_mul_log_one_add_le_parameterA
    {m : ℕ} (hm : 1 ≤ m) :
    200 * Real.log
        (1 + (m : ℝ) / (parameterA m : ℝ)) ≤ parameterA m := by sorry
