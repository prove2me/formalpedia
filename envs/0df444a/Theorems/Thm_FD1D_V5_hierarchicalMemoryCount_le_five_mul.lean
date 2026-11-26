-- Prove2me | Theorems.Thm_FD1D_V5_hierarchicalMemoryCount_le_five_mul
-- name    : FD1D.V5.hierarchicalMemoryCount_le_five_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:18:56.900747+00:00
-- url     : https://prove2.me/theorems/2efa04c7-9139-438f-8b86-469d023d0de8
-- title:
--   V5: hierarchical Memory Count le five mul
-- statement:
--   The abstract memory budget is at most `5m` words.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/Complexity.lean#L39-L45
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/Complexity.lean#L39-L45

import Definitions.Def_FD1D_V5_Parameters
import Definitions.Def_FD1D_V5_Complexity
set_option autoImplicit true
open FD1D FD1D.V5
noncomputable section
open Filter Asymptotics

theorem FD1D.V5.hierarchicalMemoryCount_le_five_mul
    {m : ℕ} (hm : 1 ≤ m) :
    hierarchicalMemoryCount m ≤ 5 * m := by sorry
