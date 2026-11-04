-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_ubv_sigma_zero_original_stopped_second_order_vanishes
-- name    : AvramDividend.Classical.avram_p4_a_gaussian_ubv_sigma_zero_original_stopped_second_order_vanishes
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:45:15.990513+00:00
-- url     : https://prove2.me/theorems/756c0a0a-1c70-439b-8489-59e74caf0ab7
-- title:
--   Original controlled pure-jump UBV branch: stopped Gaussian correction is integrable and zero
-- statement:
--   For the actual source Lévy X with unbounded variation and sigma=0, its original controlled surplus riskProcess X x D, arbitrary finite stopped clock tau, and any explicit time measure mu on nonnegative times, the discounted Gaussian second-order correction vanishes identically, is integrable and has zero pathwise integral. The arbitrary time measure resolves the source environment's lack of an implicit MeasureSpace ℝ≥0; no Brownian process or boundary assumptions are introduced.
-- source:
--   Avram et al Eq (5.11), generator Gaussian coefficient sigma²/2; source SpectrallyNegativeLevy, DividendStrategy; corrected formal measure argument after failed authoring job e7e4d0da-039a-48b0-9e2e-58013307076c.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_a_gaussian_ubv_sigma_zero_original_stopped_second_order_vanishes
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hUBV : ¬ X.BoundedVariation)
    (hZero : X.σ = 0)
    (q : ℝ) (w : ℝ → ℝ) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (τ : Ω → ℝ≥0)
    (μ : Measure ℝ≥0) (ω : Ω) :
    IntegrableOn
      (fun s : ℝ≥0 => Real.exp (-(q * (s : ℝ))) *
        (X.σ ^ 2 / 2 * iteratedDeriv 2 w (riskProcess X x D s ω)))
      (Icc 0 (τ ω)) μ ∧
    (∫ s in Icc 0 (τ ω), Real.exp (-(q * (s : ℝ))) *
      (X.σ ^ 2 / 2 * iteratedDeriv 2 w (riskProcess X x D s ω)) ∂μ) = 0 := by sorry
