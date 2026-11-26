-- Prove2me | Theorems.Thm_FD1D_V5_parameterA_cast_le_log_succ
-- name    : FD1D.V5.parameterA_cast_le_log_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:47:20.473288+00:00
-- url     : https://prove2.me/theorems/304dbd13-52b8-5bec-8544-9ec16999ee24
-- title:
--   V5: parameter A cast le log succ
-- statement:
--   The same bound in the manuscript's displayed `log(m+1)` form.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/Parameters.lean#L210-L221
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/Parameters.lean#L210-L221

import Definitions.Def_FD1D_Tree
import Definitions.Def_FD1D_V5_Parameters
set_option autoImplicit true
open FD1D FD1D.V5
noncomputable section
open Filter Asymptotics

theorem FD1D.V5.parameterA_cast_le_log_succ {m : ℕ} (hm : 2 ≤ m) :
    (parameterA m : ℝ) ≤
      (8000 / Real.log 2) * Real.log ((m + 1 : ℕ) : ℝ) := by sorry
