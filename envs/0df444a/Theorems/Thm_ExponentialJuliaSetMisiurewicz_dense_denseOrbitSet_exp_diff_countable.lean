-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_dense_denseOrbitSet_exp_diff_countable
-- name    : ExponentialJuliaSetMisiurewicz.dense_denseOrbitSet_exp_diff_countable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:04:08.068539+00:00
-- url     : https://prove2.me/theorems/f3ab93db-6913-5f65-9298-47b06856f785
-- title:
--   Exponential Julia Set Misiurewicz: dense dense Orbit Set exp diff countable
-- statement:
--   Removing a countable set still leaves a dense set of points with dense orbit.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Dynamics.lean#L155-L187
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Dynamics.lean#L155-L187

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

theorem ExponentialJuliaSetMisiurewicz.dense_denseOrbitSet_exp_diff_countable {C : Set ℂ} (hC : C.Countable) :
    Dense (denseOrbitSetExp \ C) := by sorry
