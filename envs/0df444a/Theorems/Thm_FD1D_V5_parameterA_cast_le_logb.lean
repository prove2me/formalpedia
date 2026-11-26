-- Prove2me | Theorems.Thm_FD1D_V5_parameterA_cast_le_logb
-- name    : FD1D.V5.parameterA_cast_le_logb
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:16:06.298432+00:00
-- url     : https://prove2.me/theorems/c7b0ee5f-42fb-491e-ab31-aad7f15f82da
-- title:
--   V5: parameter A cast le logb
-- statement:
--   A convenient explicit base-two logarithmic upper bound.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/Parameters.lean#L167-L196
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/Parameters.lean#L167-L196

import Definitions.Def_FD1D_Tree
import Definitions.Def_FD1D_V5_Parameters
set_option autoImplicit true
open FD1D FD1D.V5
noncomputable section
open Filter Asymptotics

theorem FD1D.V5.parameterA_cast_le_logb {m : ℕ} (hm : 2 ≤ m) :
    (parameterA m : ℝ) ≤ 8000 * Real.logb 2 m := by sorry
