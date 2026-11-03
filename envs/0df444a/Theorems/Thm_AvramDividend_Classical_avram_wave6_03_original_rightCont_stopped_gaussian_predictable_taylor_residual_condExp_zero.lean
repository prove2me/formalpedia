-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_predictable_taylor_residual_condExp_zero
-- name    : AvramDividend.Classical.avram_wave6_03_original_rightCont_stopped_gaussian_predictable_taylor_residual_condExp_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T08:21:19.41246+00:00
-- url     : https://prove2.me/theorems/32d08f0c-79ae-44fa-84f1-bf04ff639cf9
-- title:
--   Original stopped Gaussian predictable gradient plus compensated Hessian Taylor residual has L1 and conditional mean zero
-- statement:
--   For the original same-sample spectrally negative Levy process with zero jump measure, any bounded right-continuous source stopping time and two stopped-history measurable weights G and H, assuming the actual weighted linear and square source increments and H are integrable, prove the sum G times the genuine centered Gaussian source increment and H times its compensated square is integrable and has conditional mean zero given the same stopped sigma-algebra. Choosing H as one-half the actual clipped discounted pre-dividend Hessian yields the exact stochastic Taylor martingale difference, for arbitrary source sigma including sigma zero. This unifies two independently proved physical stopped increment martingale differences without a detached Brownian process. No claim of a pathwise continuum Ito formula or of a continuous residual for general nonzero Levy jump measure is made.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_history_weighted_condExp_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_predictable_compensated_quadratic_condExp_zero

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave6_03_original_rightCont_stopped_gaussian_predictable_taylor_residual_condExp_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (B : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ B)
    (h : ℝ≥0) (G H : Ω → ℝ)
    (hG : Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] G)
    (hH : Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] H)
    (hGI : Integrable (fun ω =>
      G ω * (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c)) P)
    (hHI : Integrable H P)
    (hH2I : Integrable (fun ω =>
      H ω * (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c) ^ 2) P) :
    let Y : Ω → ℝ := fun ω =>
      X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
    let A : Ω → ℝ := fun ω => G ω * Y ω
    let R : Ω → ℝ := fun ω => H ω * Y ω ^ 2 - ((h : ℝ) * X.σ ^ 2) * H ω
    Integrable (A + R) P ∧
      P[A + R | (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]
        =ᵐ[P] (fun _ => (0 : ℝ)) := by
  sorry
