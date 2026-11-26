-- Prove2me | Theorems.Thm_FD1D_weighted_tree_telescope
-- name    : FD1D.weighted_tree_telescope
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:49:14.466125+00:00
-- url     : https://prove2.me/theorems/bd53a217-aee4-5204-9cc5-bdf0c436eacb
-- title:
--   FD1 D: weighted tree telescope
-- statement:
--   Generic mass-weighted telescope over all internal nodes.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Tree.lean#L409-L416
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Tree.lean#L409-L416

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Tree
set_option autoImplicit true
open FD1D
noncomputable section

theorem FD1D.weighted_tree_telescope
    (f : ∀ d, DyadicNode d → ℝ) (L : ℕ) :
    ∑ d ∈ Finset.range L,
        ∑ v, nodeMass d v * (childAverage f d v - f d v) =
      weightedLevel f L - f 0 dyadicRoot := by sorry
