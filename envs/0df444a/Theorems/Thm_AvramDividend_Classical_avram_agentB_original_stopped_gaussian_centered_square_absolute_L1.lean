-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_agentB_original_stopped_gaussian_centered_square_absolute_L1
-- name    : AvramDividend.Classical.avram_agentB_original_stopped_gaussian_centered_square_absolute_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T12:43:29.849584+00:00
-- url     : https://prove2.me/theorems/af82e3a1-b07d-48f5-9555-f22ac7eb70a6
-- title:
--   Original stopped pure Gaussian centred quadratic Hermite increment has absolute L1 at most twice sigma-square mesh
-- statement:
--   For the true original spectrally negative zero-jump Lévy process, stopped at any bounded right-continuous original filtration stopping time, the absolute centred quadratic Hermite increment has finite expectation bounded by twice the exact Gaussian sigma-square times the physical increment h. This uses the already Proved exact original stopped Gaussian variance and a generic nonnegative-square absolute-moment inequality. It is the O(Δ) local expected envelope for the Hessian part of the original pre/post dividend grid source.
-- source:
--   Proved avram_wave6_03_original_rightCont_stopped_gaussian_exact_variance and avram_agentB_gaussian_centered_square_abs_moment_le_twice_variance.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_agentB_original_stopped_gaussian_centered_square_absolute_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0)
    (hInt : Integrable
      (fun ω => (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c) ^ 2) P) :
    Integrable (fun ω => abs (
      (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c) ^ 2 -
      (h : ℝ) * X.σ ^ 2)) P ∧
    (∫ ω, abs ((X.X (τ ω + h) ω - X.X (τ ω) ω -
      (h : ℝ) * X.c) ^ 2 - (h : ℝ) * X.σ ^ 2) ∂P) ≤
      2 * ((h : ℝ) * X.σ ^ 2) := by sorry
