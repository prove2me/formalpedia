-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_equicontinuous_of_bounded
-- name    : ExponentialJuliaSetMisiurewicz.equicontinuous_of_bounded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:02:24.966812+00:00
-- url     : https://prove2.me/theorems/e25abb70-c175-5fec-a9aa-0731977b9dce
-- title:
--   Exponential Julia Set Misiurewicz: equicontinuous of bounded
-- statement:
--   **Weak Montel, equicontinuity form.** A uniformly bounded family of holomorphic functions
--   on `ball c (2ρ)` is equicontinuous on `ball c ρ`, with a modulus independent of the index.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/HalfPlane.lean#L85-L110
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/HalfPlane.lean#L85-L110

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

theorem ExponentialJuliaSetMisiurewicz.equicontinuous_of_bounded
    {ι : Type*} {F : ι → ℂ → ℂ} {M ρ : ℝ} {c : ℂ} (hρ : 0 < ρ)
    (hF : ∀ i, DifferentiableOn ℂ (F i) (ball c (2 * ρ)))
    (hb : ∀ i, ∀ w ∈ ball c (2 * ρ), ‖F i w‖ ≤ M)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ i : ι, ∀ x ∈ ball c ρ, ∀ y ∈ ball c ρ,
      ‖x - y‖ < δ → ‖F i x - F i y‖ < ε := by sorry
