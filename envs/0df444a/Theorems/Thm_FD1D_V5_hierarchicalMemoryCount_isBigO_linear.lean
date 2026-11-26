-- Prove2me | Theorems.Thm_FD1D_V5_hierarchicalMemoryCount_isBigO_linear
-- name    : FD1D.V5.hierarchicalMemoryCount_isBigO_linear
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:22:57.017791+00:00
-- url     : https://prove2.me/theorems/d63e0495-27bf-4992-a48c-e5b4fdd1384b
-- title:
--   V5: hierarchical Memory Count is Big O linear
-- statement:
--   Memory is `O(m)` in the accounting model.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/Complexity.lean#L110-L117
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/Complexity.lean#L110-L117

import Definitions.Def_FD1D_V5_Parameters
import Definitions.Def_FD1D_V5_Complexity
set_option autoImplicit true
open FD1D FD1D.V5
noncomputable section
open Filter Asymptotics

theorem FD1D.V5.hierarchicalMemoryCount_isBigO_linear :
    (fun m : ℕ => (hierarchicalMemoryCount m : ℝ)) =O[atTop]
      (fun m : ℕ => (m : ℝ)) := by sorry
