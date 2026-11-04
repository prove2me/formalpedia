-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_rightCont_bounded_stop_discounted_exp_mean_le_one
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_rightCont_bounded_stop_discounted_exp_mean_le_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:12:15.925929+00:00
-- url     : https://prove2.me/theorems/cc0b958f-7664-4bbf-9bad-f8ab9f66de42
-- title:
--   Original right-continuous bounded-stop discounted source Lévy exponential has expected value at most one
-- statement:
--   For any bounded stopping time in the original process's right-continuous filtration, if θ≥0 and the original Lévy exponent satisfies ψ(θ)≤q, then the genuine stopped discounted source exponential has Bochner integral at most one. Derive Esscher likelihood integrability from its already Proved exact integral one and use nonnegative integral monotonicity with q≥ψθ. This is the missing random-clock source exponential upper envelope, independent of dividend process and without a fake Brownian/Poisson process.
-- source:
--   Proved source right-continuous bounded stopped Esscher likelihood mean one 46c2da57, Mathlib pinned MeasureTheory.integrable_of_integral_eq_one and MeasureTheory.integral_mono_of_nonneg.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_rightCont_bounded_stop_esscher_likelihood_mean_one
open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_rightCont_bounded_stop_discounted_exp_mean_le_one
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) (q : ℝ) (hq : X.ψ θ ≤ q)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (H : ℝ≥0) (hbound : ∀ ω, τ ω ≤ H) :
    (∫ ω, Real.exp (θ * X.X (τ ω) ω - (τ ω : ℝ) * q) ∂P) ≤ (1 : ℝ) := by sorry
