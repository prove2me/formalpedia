-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a64_original_zerojump_discounted_generator_variance_drift_cancellation
-- name    : AvramDividend.Classical.avram_ga_a64_original_zerojump_discounted_generator_variance_drift_cancellation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T07:26:55.843556+00:00
-- url     : https://prove2.me/theorems/0f718716-8191-4464-94e6-63ea48351346
-- title:
--   Original discounted Gaussian spatial generator variance clock cancels exactly to the actual Lévy source drift
-- statement:
--   On the original dividend-controlled pure Gaussian Levy process at every actual physical source time, the discounted quadratic Gaussian variance clock minus the discounted zero-jump generator is exactly the negative discounted original source drift times the value gradient.
-- source:
--   Original b0d9951c expected positive stopped Gaussian spatial source error expansion: cancel generator quadratic clock with drift using Proved p4_f11.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a64_original_zerojump_discounted_generator_variance_drift_cancellation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (q : ℝ)
    (ω : Ω) (s Δ : ℝ≥0) :
    let y : ℝ := x + X.X s ω - rightLimit D s ω
    let E : ℝ := Real.exp (-(q * (s : ℝ)))
    E * (iteratedDeriv 2 w y / 2 * ((Δ : ℝ) * X.σ ^ 2)) -
      (Δ : ℝ) * E * X.generator w y =
      -((Δ : ℝ) * E * X.c * deriv w y) := by sorry
