-- Prove2me | Theorems.Thm_FD1D_V5_log_one_add_two_mul_div_le_parameterA_div_two_thousand
-- name    : FD1D.V5.log_one_add_two_mul_div_le_parameterA_div_two_thousand
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:47:17.378645+00:00
-- url     : https://prove2.me/theorems/71a91a4a-f4d3-50a8-a6ba-c8ceb45e7f45
-- title:
--   V5: log one add two mul div le parameter A div two thousand
-- statement:
--   The potential budget used in the transient energy estimate.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/Parameters.lean#L115-L164
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/Parameters.lean#L115-L164

import Definitions.Def_FD1D_Tree
import Definitions.Def_FD1D_V5_Parameters
set_option autoImplicit true
open FD1D FD1D.V5
noncomputable section
open Filter Asymptotics

theorem FD1D.V5.log_one_add_two_mul_div_le_parameterA_div_two_thousand
    {m : ℕ} (hm : 1 ≤ m) :
    Real.log
        (1 + 2 * (m : ℝ) / (parameterA m : ℝ)) ≤
      (parameterA m : ℝ) / 2000 := by sorry
