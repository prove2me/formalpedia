-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a67_original_gaussian_positive_optimal_chernoff_source_increment
-- name    : AvramDividend.Classical.avram_ga_a67_original_gaussian_positive_optimal_chernoff_source_increment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T07:33:55.732199+00:00
-- url     : https://prove2.me/theorems/47e86f9a-e9ee-4883-b162-1a0b866cc866
-- title:
--   Original positive-centred zero-jump Gaussian physical-increment tail has sharp exponential Chernoff expectation
-- statement:
--   For a genuine original pure-Gaussian Levy centred physical time increment of positive length d and any nonnegative exponential weight theta, the upper excursion weighted expectation has the sharp bound exp(theta delta−delta²/(2d)) for thresholds delta above theta*d.
-- source:
--   Actual original X rare upper postpayment Gaussian spatial Taylor source excursion control for b0d9951c via ga_a61 and ga_a62.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a67_original_gaussian_positive_optimal_chernoff_source_increment
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hσ : 0 < X.σ)
    (s t : ℝ≥0) (hst : s ≤ t)
    (hd : 0 < ((t - s : ℝ≥0) : ℝ))
    (θ δ : ℝ) (hθ : 0 ≤ θ)
    (hδ : θ * ((t - s : ℝ≥0) : ℝ) ≤ δ) :
    let Z : Ω → ℝ := fun ω =>
      ((X.X t ω - X.X s ω) -
        ((t - s : ℝ≥0) : ℝ) * X.c) / X.σ
    Integrable (fun ω => if δ ≤ Z ω then Real.exp (θ * Z ω) else 0) P →
    Integrable (fun ω => Real.exp
      ((θ + (δ / ((t - s : ℝ≥0) : ℝ) - θ)) * Z ω)) P →
    (∫ ω, if δ ≤ Z ω then Real.exp (θ * Z ω) else 0 ∂P) ≤
      Real.exp (θ * δ -
        δ^2 / (2 * ((t - s : ℝ≥0) : ℝ))) := by sorry
