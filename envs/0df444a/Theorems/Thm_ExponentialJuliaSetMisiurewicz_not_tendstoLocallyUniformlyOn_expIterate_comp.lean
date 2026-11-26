-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_not_tendstoLocallyUniformlyOn_expIterate_comp
-- name    : ExponentialJuliaSetMisiurewicz.not_tendstoLocallyUniformlyOn_expIterate_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:01:27.778372+00:00
-- url     : https://prove2.me/theorems/124e85de-c6ce-5c47-85c0-6e75a7d1801a
-- title:
--   Exponential Julia Set Misiurewicz: not tendsto Locally Uniformly On exp Iterate comp
-- statement:
--   Eventual point covering obstructs all locally uniform subsequential limits in any
--   separated uniform target, provided the continuous target map distinguishes `1` and `2`.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Spherical.lean#L118-L147
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Spherical.lean#L118-L147

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

theorem ExponentialJuliaSetMisiurewicz.not_tendstoLocallyUniformlyOn_expIterate_comp
    {Y : Type*} [UniformSpace Y] [T0Space Y]
    {q : ℂ → Y} (hqcont : Continuous q) (hq : q 1 ≠ q 2)
    {U : Set ℂ} (hU : IsOpen U) (hUne : U.Nonempty)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) (g : ℂ → Y) :
    ¬ TendstoLocallyUniformlyOn (fun n z => q (expIterate (φ n) z)) g atTop U := by sorry
