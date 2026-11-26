-- Prove2me | Theorems.Thm_FD1D_weighted_childAverage_sum
-- name    : FD1D.weighted_childAverage_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:48:44.73673+00:00
-- url     : https://prove2.me/theorems/5f256433-cd53-49a2-8b9f-5f43f09feb68
-- title:
--   FD1 D: weighted child Average sum
-- statement:
--   A child average weighted at the parent equals the next weighted level.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Tree.lean#L385-L392
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Tree.lean#L385-L392

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Tree
set_option autoImplicit true
open FD1D
noncomputable section

theorem FD1D.weighted_childAverage_sum
    (f : ∀ d, DyadicNode d → ℝ) (d : ℕ) :
    ∑ v, nodeMass d v * childAverage f d v = weightedLevel f (d + 1) := by sorry
