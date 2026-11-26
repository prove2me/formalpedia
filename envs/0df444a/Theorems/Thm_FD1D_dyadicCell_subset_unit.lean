-- Prove2me | Theorems.Thm_FD1D_dyadicCell_subset_unit
-- name    : FD1D.dyadicCell_subset_unit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:14:15.828286+00:00
-- url     : https://prove2.me/theorems/c065a736-8c32-51b3-9d80-1999b2625e62
-- title:
--   FD1 D: dyadic Cell subset unit
-- statement:
--   The FD1 D construction uses the dyadic Cell subset unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Spatial.lean#L385-L403
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Spatial.lean#L385-L403

import Definitions.Def_FD1D_Transport
import Definitions.Def_FD1D_Markov
import Definitions.Def_FD1D_Tree
import Definitions.Def_FD1D_Spatial
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory

theorem FD1D.dyadicCell_subset_unit {L : ℕ} (i : DyadicNode L) :
    dyadicCell i ⊆ Icc (0 : ℝ) 1 := by sorry
