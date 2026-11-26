-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_not_tendstoLocallyUniformly_expIterate_comp
-- name    : ExponentialJuliaSetMisiurewicz.not_tendstoLocallyUniformly_expIterate_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:01:51.382595+00:00
-- url     : https://prove2.me/theorems/90d82ca7-e869-460a-ac60-a0163ee7451f
-- title:
--   Exponential Julia Set Misiurewicz: not tendsto Locally Uniformly exp Iterate comp
-- statement:
--   The two-target obstruction with the limit function defined only on its domain `U`.
--   The auxiliary extension in the proof serves solely to use Mathlib's ambient-domain API.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Spherical.lean#L151-L166
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Spherical.lean#L151-L166

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

theorem ExponentialJuliaSetMisiurewicz.not_tendstoLocallyUniformly_expIterate_comp
    {Y : Type*} [UniformSpace Y] [T0Space Y]
    {q : ℂ → Y} (hqcont : Continuous q) (hq : q 1 ≠ q 2)
    {U : Set ℂ} (hU : IsOpen U) (hUne : U.Nonempty)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) (g : U → Y) :
    ¬ TendstoLocallyUniformly (fun n (z : U) => q (expIterate (φ n) z)) g atTop := by sorry
