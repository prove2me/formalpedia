-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_escapesToInfinity_of_eventually_onRealAxis
-- name    : ExponentialJuliaSetMisiurewicz.escapesToInfinity_of_eventually_onRealAxis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:04:01.276231+00:00
-- url     : https://prove2.me/theorems/ab37a2b9-9891-565e-af57-fbf5ef57ac4c
-- title:
--   Exponential Julia Set Misiurewicz: escapes To Infinity of eventually on Real Axis
-- statement:
--   Any point whose orbit reaches the real axis subsequently escapes to infinity.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Dynamics.lean#L64-L78
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Dynamics.lean#L64-L78

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

theorem ExponentialJuliaSetMisiurewicz.escapesToInfinity_of_eventually_onRealAxis {z : ℂ} {m : ℕ}
    (hm : OnRealAxis (expIterate m z)) : EscapesToInfinity z := by sorry
