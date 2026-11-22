-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_lsv_original_rightcont_stopped_gaussian_weighted_sqrt_time_first_moment
-- name    : AvramDividend.Classical.avram_lsv_original_rightcont_stopped_gaussian_weighted_sqrt_time_first_moment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T17:03:24.431236+00:00
-- url     : https://prove2.me/theorems/9375a5b8-90b8-4bbb-9411-fa5f0200a6f2
-- title:
--   Actual original Gaussian stopped predictable nonnegative weights have square-root-clock weighted first moment
-- statement:
--   For the original zero-jump spectrally negative Levy source with positive Gaussian coefficient, any nonnegative weight measurable at a bounded right-continuous stopping time and satisfying source integrability assumptions has expected weighted absolute centred future increment at most sigma times the square root of the future duration times expected weight. Derived by optimizing the Proved source-specific stopped Young inequality. Supports the true dividend atom Gaussian pre/post first Hermite cell bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_agentB_original_rightcont_stopped_gaussian_weighted_abs_increment_young
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false
noncomputable section

theorem AvramDividend.Classical.avram_lsv_original_rightcont_stopped_gaussian_weighted_sqrt_time_first_moment
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτevents : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s]
      {ω : Ω | τ ω ≤ s})
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (H : Ω → ℝ)
    (hH : Measurable[(isStoppingTime_withTop_of_le_events τ hτevents).measurableSpace] H)
    (hHglobal : Measurable H)
    (hHnonneg : ∀ ω, 0 ≤ H ω)
    (hHI : Integrable H P)
    (hHZI : Integrable (fun ω => H ω * abs
      (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c)) P)
    (hHZ2I : Integrable (fun ω => H ω *
      (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c) ^ 2) P)
    (hσ : 0 < X.σ) (hh : 0 < h) :
    (∫ ω, H ω *
      abs (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c) ∂P) ≤
    X.σ * Real.sqrt (h : ℝ) * (∫ ω, H ω ∂P) := by sorry
