-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_not_isNormalSequenceOn_sphericalExpIterate
-- name    : ExponentialJuliaSetMisiurewicz.not_isNormalSequenceOn_sphericalExpIterate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:04:20.873356+00:00
-- url     : https://prove2.me/theorems/2ece3e7a-1483-5641-9893-662693f3c8df
-- title:
--   Exponential Julia Set Misiurewicz: not is Normal Sequence On spherical Exp Iterate
-- statement:
--   The sphere-valued exponential iterates are not normal on a nonempty open set.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Normality.lean#L83-L90
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Normality.lean#L83-L90

import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Definitions.Def_ExpChaotic_Spherical
import Definitions.Def_ExpChaotic_Normality
set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section

theorem ExponentialJuliaSetMisiurewicz.not_isNormalSequenceOn_sphericalExpIterate
    {U : Set ℂ} (hU : IsOpen U) (hUne : U.Nonempty) :
    ¬ IsNormalSequenceOn sphericalExpIterate U := by sorry
