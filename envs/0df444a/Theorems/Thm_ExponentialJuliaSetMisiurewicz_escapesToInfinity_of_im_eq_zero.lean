-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_escapesToInfinity_of_im_eq_zero
-- name    : ExponentialJuliaSetMisiurewicz.escapesToInfinity_of_im_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:04:10.550175+00:00
-- url     : https://prove2.me/theorems/1109b6f1-41ef-48c7-92a4-900e7c2b27ad
-- title:
--   Exponential Julia Set Misiurewicz: escapes To Infinity of im eq zero
-- statement:
--   Every real point escapes to infinity under iteration of the exponential map.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Dynamics.lean#L52-L61
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Dynamics.lean#L52-L61

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

theorem ExponentialJuliaSetMisiurewicz.escapesToInfinity_of_im_eq_zero {z : ℂ} (hz : z.im = 0) :
    EscapesToInfinity z := by sorry
