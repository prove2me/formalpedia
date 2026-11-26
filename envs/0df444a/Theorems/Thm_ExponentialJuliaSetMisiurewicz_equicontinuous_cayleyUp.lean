-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_equicontinuous_cayleyUp
-- name    : ExponentialJuliaSetMisiurewicz.equicontinuous_cayleyUp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:02:39.543344+00:00
-- url     : https://prove2.me/theorems/7bb8fbd9-3229-5aa5-832f-0d83aa94998d
-- title:
--   Exponential Julia Set Misiurewicz: equicontinuous cayley Up
-- statement:
--   **The transformed family is uniformly bounded, hence equicontinuous.** Along any set of
--   times whose images all lie in the upper half-plane, the Cayley transforms of the iterates are
--   bounded by `1` on `ball c (2ρ)`, so `equicontinuous_of_bounded` applies on `ball c ρ`.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/HalfPlane.lean#L237-L246
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/HalfPlane.lean#L237-L246

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

theorem ExponentialJuliaSetMisiurewicz.equicontinuous_cayleyUp {c : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    {T : Set ℕ} (hT : ∀ n ∈ T, ∀ z ∈ ball c (2 * ρ), 0 < (expIterate n z).im)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ n : T, ∀ x ∈ ball c ρ, ∀ y ∈ ball c ρ, ‖x - y‖ < δ →
      ‖(expIterate n.1 x - Complex.I) / (expIterate n.1 x + Complex.I)
        - (expIterate n.1 y - Complex.I) / (expIterate n.1 y + Complex.I)‖ < ε := by sorry
