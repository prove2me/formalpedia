-- Prove2me | Theorems.Thm_FD1D_sum_nodeMass
-- name    : FD1D.sum_nodeMass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:49:53.54792+00:00
-- url     : https://prove2.me/theorems/c8d08cf4-7c5a-5315-b3a1-844455a10977
-- title:
--   FD1 D: sum node Mass
-- statement:
--   Node masses at every complete level sum to one.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Tree.lean#L236-L238
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Tree.lean#L236-L238

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Tree
set_option autoImplicit true
open FD1D
noncomputable section

theorem FD1D.sum_nodeMass (d : ℕ) :
    ∑ v : DyadicNode d, nodeMass d v = 1 := by sorry
