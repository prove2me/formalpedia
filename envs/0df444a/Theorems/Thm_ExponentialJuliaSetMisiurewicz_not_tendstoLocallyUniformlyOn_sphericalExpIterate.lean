-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_not_tendstoLocallyUniformlyOn_sphericalExpIterate
-- name    : ExponentialJuliaSetMisiurewicz.not_tendstoLocallyUniformlyOn_sphericalExpIterate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:02:00.903459+00:00
-- url     : https://prove2.me/theorems/75d47cec-865f-482e-8786-1fe7e308fe5c
-- title:
--   Exponential Julia Set Misiurewicz: not tendsto Locally Uniformly On spherical Exp Iterate
-- statement:
--   No increasing subsequence of exponential iterates converges locally uniformly in
--   the spherical uniformity on a nonempty open set, to any sphere-valued function.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Spherical.lean#L170-L176
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Spherical.lean#L170-L176

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

theorem ExponentialJuliaSetMisiurewicz.not_tendstoLocallyUniformlyOn_sphericalExpIterate
    {U : Set ℂ} (hU : IsOpen U) (hUne : U.Nonempty)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) (g : ℂ → RiemannSphere) :
    ¬ TendstoLocallyUniformlyOn (fun n => sphericalExpIterate (φ n)) g atTop U := by sorry
