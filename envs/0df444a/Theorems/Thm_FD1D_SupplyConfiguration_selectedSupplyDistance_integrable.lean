-- Prove2me | Theorems.Thm_FD1D_SupplyConfiguration_selectedSupplyDistance_integrable
-- name    : FD1D.SupplyConfiguration.selectedSupplyDistance_integrable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:16:01.967949+00:00
-- url     : https://prove2.me/theorems/5d45ca35-546b-4893-91bd-8e223cc72d42
-- title:
--   Supply Configuration: selected Supply Distance integrable
-- statement:
--   The Supply Configuration construction uses the selected Supply Distance integrable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Spatial.lean#L595-L609
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Spatial.lean#L595-L609

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

theorem FD1D.SupplyConfiguration.selectedSupplyDistance_integrable
    (C : SupplyConfiguration L m) (q : DyadicMass L)
    (fallback : Fin m) :
    IntegrableOn
      (fun u => |C.selectedSupplyPoint q fallback u - u|)
      (Icc (0 : ℝ) 1) := by sorry
