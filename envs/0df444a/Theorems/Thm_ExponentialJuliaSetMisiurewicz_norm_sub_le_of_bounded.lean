-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_norm_sub_le_of_bounded
-- name    : ExponentialJuliaSetMisiurewicz.norm_sub_le_of_bounded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:02:23.56883+00:00
-- url     : https://prove2.me/theorems/0f16e490-b1f4-41cc-94b3-424cfa806498
-- title:
--   Exponential Julia Set Misiurewicz: norm sub le of bounded
-- statement:
--   A holomorphic function bounded by `M` on `ball c (2ρ)` is `2M/ρ`-Lipschitz on `ball c ρ`.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/HalfPlane.lean#L51-L81
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/HalfPlane.lean#L51-L81

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Algebra.Order.Star.Real
import Definitions.Def_ExpChaotic_StripGeometry
import Definitions.Def_ExpChaotic_HalfPlane
set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section

theorem ExponentialJuliaSetMisiurewicz.norm_sub_le_of_bounded
    {f : ℂ → ℂ} {M ρ : ℝ} {c : ℂ} (hρ : 0 < ρ)
    (hf : DifferentiableOn ℂ f (ball c (2 * ρ)))
    (hb : ∀ w ∈ ball c (2 * ρ), ‖f w‖ ≤ M)
    {x y : ℂ} (hx : x ∈ ball c ρ) (hy : y ∈ ball c ρ) :
    ‖f x - f y‖ ≤ (2 * M / ρ) * ‖x - y‖ := by sorry
