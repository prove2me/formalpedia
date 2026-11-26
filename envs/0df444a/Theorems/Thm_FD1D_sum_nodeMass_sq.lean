-- Prove2me | Theorems.Thm_FD1D_sum_nodeMass_sq
-- name    : FD1D.sum_nodeMass_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:49:40.056004+00:00
-- url     : https://prove2.me/theorems/01a46638-b9cc-5baf-b969-f19adb51ce06
-- title:
--   FD1 D: sum node Mass sq
-- statement:
--   Squared interval masses on level `d` sum to `2⁻ᵈ`.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Tree.lean#L687-L690
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Tree.lean#L687-L690

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Tree
set_option autoImplicit true
open FD1D
noncomputable section

theorem FD1D.sum_nodeMass_sq (d : ℕ) :
    ∑ v : DyadicNode d, (nodeMass d v) ^ 2 = ((2 : ℝ) ^ d)⁻¹ := by sorry
