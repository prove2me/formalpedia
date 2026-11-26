-- Prove2me | Theorems.Thm_FD1D_V5_hierarchicalOperationCount_cast_le_log
-- name    : FD1D.V5.hierarchicalOperationCount_cast_le_log
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:18:25.902519+00:00
-- url     : https://prove2.me/theorems/697d4c9a-1701-5bf7-8dd0-fabe7e6df0fd
-- title:
--   V5: hierarchical Operation Count cast le log
-- statement:
--   Explicit natural-log bound for the real-valued operation count.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/Complexity.lean#L48-L95
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/Complexity.lean#L48-L95

import Definitions.Def_FD1D_V5_Parameters
import Definitions.Def_FD1D_V5_Complexity
set_option autoImplicit true
open FD1D FD1D.V5
noncomputable section
open Filter Asymptotics

theorem FD1D.V5.hierarchicalOperationCount_cast_le_log
    {m : ℕ} (hm : 2 ≤ m) :
    (hierarchicalOperationCount m : ℝ) ≤
      (100 / Real.log 2) * Real.log (m : ℝ) := by sorry
