-- Prove2me | Theorems.Thm_FD1D_SupplyConfiguration_quantileDistance_integrable
-- name    : FD1D.SupplyConfiguration.quantileDistance_integrable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:16:15.933088+00:00
-- url     : https://prove2.me/theorems/a58d65d5-bc7c-4770-bda4-37c1fb53f55d
-- title:
--   Supply Configuration: quantile Distance integrable
-- statement:
--   The Supply Configuration construction uses the quantile Distance integrable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Spatial.lean#L611-L623
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Spatial.lean#L611-L623

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

theorem FD1D.SupplyConfiguration.quantileDistance_integrable
    (q : DyadicMass L) (hq : q.IsProbability) :
    IntegrableOn (fun u => |q.quantile u - u|) (Icc (0 : ℝ) 1) := by sorry
