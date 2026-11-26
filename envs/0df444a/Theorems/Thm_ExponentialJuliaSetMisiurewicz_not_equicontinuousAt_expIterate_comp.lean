-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_not_equicontinuousAt_expIterate_comp
-- name    : ExponentialJuliaSetMisiurewicz.not_equicontinuousAt_expIterate_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:01:19.735953+00:00
-- url     : https://prove2.me/theorems/1cb7c580-a9d8-5e06-99b0-4493dc9bd916
-- title:
--   Exponential Julia Set Misiurewicz: not equicontinuous At exp Iterate comp
-- statement:
--   The two-target obstruction to equicontinuity, for any separated uniform target
--   and any target map distinguishing `1` and `2`. The domain is the Euclidean plane.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Spherical.lean#L52-L67
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Spherical.lean#L52-L67

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

theorem ExponentialJuliaSetMisiurewicz.not_equicontinuousAt_expIterate_comp
    {Y : Type*} [UniformSpace Y] [T0Space Y]
    {q : ℂ → Y} (hq : q 1 ≠ q 2) (z : ℂ) :
    ¬ EquicontinuousAt (fun n w => q (expIterate n w)) z := by sorry
