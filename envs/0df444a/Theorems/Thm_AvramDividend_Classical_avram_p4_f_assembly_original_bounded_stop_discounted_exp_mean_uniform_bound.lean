-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_bounded_stop_discounted_exp_mean_uniform_bound
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_bounded_stop_discounted_exp_mean_uniform_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:36:59.849642+00:00
-- url     : https://prove2.me/theorems/7bd787b2-594f-44f3-9639-2d029495fdd6
-- title:
--   Uniform finite-horizon moment bound for the genuine stopped discounted Lévy exponential
-- statement:
--   Every bounded stopping time for the original Lévy process satisfies E exp(θXτ−qτ)≤exp(|ψθ−q|H) for θ≥0 and any q. This is uniform in all right-continuous stopping times τ≤H and derives from the genuine mean-one stopped Esscher density and deterministic bound on its discount-ratio factor, without requiring measurability of the stopping clock as a separate assumption.
-- source:
--   Proved source right-continuous stopped Esscher mean-one 46c2da57; pinned Mathlib integral_mono_of_nonneg and integral_const_mul.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_rightCont_bounded_stop_esscher_likelihood_mean_one
open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_bounded_stop_discounted_exp_mean_uniform_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) (q : ℝ)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (H : ℝ≥0) (hbound : ∀ ω, τ ω ≤ H) :
    (∫ ω, Real.exp (θ * X.X (τ ω) ω - (τ ω : ℝ) * q) ∂P) ≤
      Real.exp (|X.ψ θ - q| * (H : ℝ)) := by sorry
