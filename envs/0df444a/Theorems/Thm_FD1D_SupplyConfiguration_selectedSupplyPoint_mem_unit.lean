-- Prove2me | Theorems.Thm_FD1D_SupplyConfiguration_selectedSupplyPoint_mem_unit
-- name    : FD1D.SupplyConfiguration.selectedSupplyPoint_mem_unit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:14:49.764236+00:00
-- url     : https://prove2.me/theorems/f1de15ba-8971-591d-870c-80cd226aad3e
-- title:
--   Supply Configuration: selected Supply Point mem unit
-- statement:
--   The Supply Configuration construction uses the selected Supply Point mem unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Spatial.lean#L489-L492
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Spatial.lean#L489-L492

import Definitions.Def_FD1D_Transport
import Definitions.Def_FD1D_Markov
import Definitions.Def_FD1D_Tree
import Definitions.Def_FD1D_Spatial
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory
open FD1D.SupplyConfiguration
variable {L m : ℕ}

theorem FD1D.SupplyConfiguration.selectedSupplyPoint_mem_unit (C : SupplyConfiguration L m)
    (q : DyadicMass L) (fallback : Fin m) (u : ℝ) :
    C.selectedSupplyPoint q fallback u ∈ Icc (0 : ℝ) 1 := by sorry
