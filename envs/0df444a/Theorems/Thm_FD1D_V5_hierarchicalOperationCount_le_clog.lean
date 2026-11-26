-- Prove2me | Theorems.Thm_FD1D_V5_hierarchicalOperationCount_le_clog
-- name    : FD1D.V5.hierarchicalOperationCount_le_clog
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:53:13.522395+00:00
-- url     : https://prove2.me/theorems/a40d0808-83f6-5fd6-a66a-af8822817d32
-- title:
--   V5: hierarchical Operation Count le clog
-- statement:
--   Operations are bounded by a constant times the base-two ceiling logarithm.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/Complexity.lean#L30-L36
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/Complexity.lean#L30-L36

import Definitions.Def_FD1D_V5_Parameters
import Definitions.Def_FD1D_V5_Complexity
set_option autoImplicit true
open FD1D FD1D.V5
noncomputable section
open Filter Asymptotics

theorem FD1D.V5.hierarchicalOperationCount_le_clog
    {m : ℕ} (hm : 1 ≤ m) :
    hierarchicalOperationCount m ≤
      20 * (Nat.clog 2 (m + 1) + 1) := by sorry
