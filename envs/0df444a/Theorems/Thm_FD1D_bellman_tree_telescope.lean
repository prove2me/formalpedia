-- Prove2me | Theorems.Thm_FD1D_bellman_tree_telescope
-- name    : FD1D.bellman_tree_telescope
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:49:19.12198+00:00
-- url     : https://prove2.me/theorems/45d78f20-4223-50ee-80d1-c153af2107f5
-- title:
--   FD1 D: bellman tree telescope
-- statement:
--   The exact generic Bellman telescope.  `c` is the child cost (`t Z` in the
--   paper), while `B` is any node potential.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Tree.lean#L523-L548
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Tree.lean#L523-L548

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Tree
set_option autoImplicit true
open FD1D
noncomputable section

theorem FD1D.bellman_tree_telescope
    (c B : ∀ d, DyadicNode d → ℝ) (L : ℕ) :
    ∑ d ∈ Finset.range L,
        ∑ v, nodeMass d v *
          (childAverage c d v + childAverage B d v - B d v) =
      nonrootWeightedSum c L + weightedLevel B L - B 0 dyadicRoot := by sorry
