-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_not_equicontinuousAt_unitSphereExpIterate
-- name    : ExponentialJuliaSetMisiurewicz.not_equicontinuousAt_unitSphereExpIterate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:08:24.064281+00:00
-- url     : https://prove2.me/theorems/180bac5a-e5de-5897-a325-f179c8137c74
-- title:
--   Exponential Julia Set Misiurewicz: not equicontinuous At unit Sphere Exp Iterate
-- statement:
--   The same non-equicontinuity statement with the ordinary metric sphere as codomain.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Spherical.lean#L99-L106
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Spherical.lean#L99-L106

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

theorem ExponentialJuliaSetMisiurewicz.not_equicontinuousAt_unitSphereExpIterate (z : ℂ) :
    ¬ EquicontinuousAt
      (fun n w => riemannSphereUniformEquivUnitSphere (sphericalExpIterate n w)) z := by sorry
