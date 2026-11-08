-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian14_original_stopped_two_weights_gaussian_bracket
-- name    : AvramDividend.Classical.avram_ubv_gaussian14_original_stopped_two_weights_gaussian_bracket
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T14:53:31.884374+00:00
-- url     : https://prove2.me/theorems/32c723fe-fabe-4919-aa35-a83db75e5152
-- title:
--   Original stopped Gaussian two-coefficient error has exact sigma-squared bracket
-- statement:
--   For Avram's unchanged original no-jump Lévy source, two predictable and globally measurable coefficients at the same bounded right-continuous stopping time satisfy an exact quadratic error identity. The expectation of squared centred Gaussian stopped increment weighted by G−H is the expectation of (G−H)² times the true hσ² bracket. It quantifies original-clock coefficient approximation error without changing the filtration or process, and can be used for L² Cauchy estimates once coefficient convergence is established.
-- source:
--   Proved original stopped Gaussian exact weighted L² isometry 4294d18f and closure of stopped-history measurability under subtraction.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_history_weighted_L2_isometry_eq

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gaussian14_original_stopped_two_weights_gaussian_bracket
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s]
      {ω : Ω | τ ω ≤ s})
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (G H : Ω → ℝ)
    (hG : Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] G)
    (hH : Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] H)
    (hGglobal : Measurable G) (hHglobal : Measurable H) :
    (∫ ω, ((G ω - H ω) *
      (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c)) ^ 2 ∂P) =
    (∫ ω, (G ω - H ω) ^ 2 ∂P) * ((h : ℝ) * X.σ ^ 2) := by sorry
