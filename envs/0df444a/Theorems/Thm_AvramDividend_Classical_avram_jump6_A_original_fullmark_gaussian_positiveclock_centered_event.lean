-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_A_original_fullmark_gaussian_positiveclock_centered_event
-- name    : AvramDividend.Classical.avram_jump6_A_original_fullmark_gaussian_positiveclock_centered_event
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T19:35:56.530339+00:00
-- url     : https://prove2.me/theorems/253da038-a915-487b-8193-c7330872419b
-- title:
--   Original fullmark Gaussian plus compensated jump gain centred on positive-clock initial events
-- statement:
--   For the actual bounded stopping clock and finite negative-jump intensity, construct the intrinsic Gaussian limit and full compensated negative-mark martingale, with their pathwise original process identity, jointly integrable stopped gain and zero mean on every initially measurable positive-clock event. This isolates the genuine centred stochastic component of the pending physical Ito-grid budget.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_ja18_original_fullmark_initial_event_stopped_reward_sources_exist
import Theorems.Thm_AvramDividend_Classical_avram_ja18_intrinsic_gaussian_bounded_true_stop_condexp_zero
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_jump6_A_original_fullmark_gaussian_positiveclock_centered_event
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (q x : ℝ) (w : ℝ → ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτbound : ∀ ω, τ ω ≤ (n : ℝ≥0))
    (F : Ω → ℝ)
    (hFsource : ∀ ω, F ω =
      Real.exp (-(q * (τ ω : ℝ))) *
        w (if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
          then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
          else riskProcess X x D (τ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal) :
    ∀ (A : Set Ω), MeasurableSet[𝓕.rightCont 0] A →
    ∃ (R Jsmall Jfull : ℝ≥0 → Ω → ℝ),
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Tendsto (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
          atTop (nhds (R t ω))) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Tendsto (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
          atTop (nhds (Jsmall t ω))) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Jfull t ω = Jsmall t ω +
          avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω +
          (t : ℝ) * (X.c - ∫ ω, X.X 1 ω ∂P)) ∧
      Integrable (fun ω => R (τ ω) ω + Jfull (τ ω) ω) P ∧
      (∫ ω in A ∩ {η : Ω | τ η ≠ 0},
        R (τ ω) ω + Jfull (τ ω) ω ∂P) = 0 := by sorry
