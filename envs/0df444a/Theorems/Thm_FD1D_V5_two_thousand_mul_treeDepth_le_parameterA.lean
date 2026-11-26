-- Prove2me | Theorems.Thm_FD1D_V5_two_thousand_mul_treeDepth_le_parameterA
-- name    : FD1D.V5.two_thousand_mul_treeDepth_le_parameterA
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:13:28.222013+00:00
-- url     : https://prove2.me/theorems/2474d0e1-6b12-424e-ad24-5a2c8cc00e7f
-- title:
--   V5: two thousand mul tree Depth le parameter A
-- statement:
--   The exact depth budget `a ≥ 2000 L`.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/Parameters.lean#L63-L67
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/Parameters.lean#L63-L67

import Definitions.Def_FD1D_Tree
import Definitions.Def_FD1D_V5_Parameters
set_option autoImplicit true
open FD1D FD1D.V5
noncomputable section
open Filter Asymptotics

theorem FD1D.V5.two_thousand_mul_treeDepth_le_parameterA {m : ℕ}
    (hm : 1 ≤ m) :
    2000 * treeDepth m ≤ parameterA m := by sorry
