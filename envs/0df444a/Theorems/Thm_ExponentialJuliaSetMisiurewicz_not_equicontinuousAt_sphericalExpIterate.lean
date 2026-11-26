-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_not_equicontinuousAt_sphericalExpIterate
-- name    : ExponentialJuliaSetMisiurewicz.not_equicontinuousAt_sphericalExpIterate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:01:27.143584+00:00
-- url     : https://prove2.me/theorems/01eb80af-570d-45e5-9ec6-27c1e6449169
-- title:
--   Exponential Julia Set Misiurewicz: not equicontinuous At spherical Exp Iterate
-- statement:
--   The exponential iterates fail to be spherically equicontinuous at every finite point.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Spherical.lean#L92-L96
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Spherical.lean#L92-L96

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Topology.Compactification.OnePoint.Sphere
import Definitions.Def_ExpChaotic_Covering
import Definitions.Def_ExpChaotic_Spherical
set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section

theorem ExponentialJuliaSetMisiurewicz.not_equicontinuousAt_sphericalExpIterate (z : ℂ) :
    ¬ EquicontinuousAt sphericalExpIterate z := by sorry
