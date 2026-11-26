-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_not_countable_denseOrbitSet_exp
-- name    : ExponentialJuliaSetMisiurewicz.not_countable_denseOrbitSet_exp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:04:43.546202+00:00
-- url     : https://prove2.me/theorems/81919c34-ffae-4be3-9305-640991a9ef48
-- title:
--   Exponential Julia Set Misiurewicz: not countable dense Orbit Set exp
-- statement:
--   **Corollary 5.6.** The set of points with dense orbit is uncountable.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Dynamics.lean#L190-L194
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Dynamics.lean#L190-L194

import Mathlib.Dynamics.Transitive
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.GroupTheory.GroupAction.IterateAct
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Definitions.Def_ExpChaotic_Periodic
import Definitions.Def_ExpChaotic_Dynamics
set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section

theorem ExponentialJuliaSetMisiurewicz.not_countable_denseOrbitSet_exp : ¬ denseOrbitSetExp.Countable := by sorry
