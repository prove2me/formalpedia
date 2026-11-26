-- Prove2me | Theorems.Thm_FD1D_DyadicMass_selectedLeaf_eq_selectedIndex
-- name    : FD1D.DyadicMass.selectedLeaf_eq_selectedIndex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:14:29.724047+00:00
-- url     : https://prove2.me/theorems/9498312d-2b82-45cc-aaf2-e47f62c30c7b
-- title:
--   Dyadic Mass: selected Leaf eq selected Index
-- statement:
--   The real endpoint returned by `selectedLeaf` is the indexed cell's left endpoint.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Spatial.lean#L171-L191
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Spatial.lean#L171-L191

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

theorem FD1D.DyadicMass.selectedLeaf_eq_selectedIndex {L : ℕ} (q : DyadicMass L) (u : ℝ) :
    q.selectedLeaf u =
      (q.selectedIndex u).val / ((2 ^ L : ℕ) : ℝ) := by sorry
