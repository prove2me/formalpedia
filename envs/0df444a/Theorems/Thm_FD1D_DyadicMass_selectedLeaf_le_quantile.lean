-- Prove2me | Theorems.Thm_FD1D_DyadicMass_selectedLeaf_le_quantile
-- name    : FD1D.DyadicMass.selectedLeaf_le_quantile
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:14:19.532268+00:00
-- url     : https://prove2.me/theorems/c39e11c5-2b50-44e5-8235-c09005d7edeb
-- title:
--   Dyadic Mass: selected Leaf le quantile
-- statement:
--   The selected endpoint never lies to the right of the continuous quantile.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Spatial.lean#L194-L214
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Spatial.lean#L194-L214

import Definitions.Def_FD1D_Transport
import Definitions.Def_FD1D_Markov
import Definitions.Def_FD1D_Tree
import Definitions.Def_FD1D_Spatial
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory
open FD1D.DyadicMass

theorem FD1D.DyadicMass.selectedLeaf_le_quantile {L : ℕ} (q : DyadicMass L)
    (hq : q.allNonneg) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ q.total) :
    q.selectedLeaf u ≤ q.quantile u := by sorry
