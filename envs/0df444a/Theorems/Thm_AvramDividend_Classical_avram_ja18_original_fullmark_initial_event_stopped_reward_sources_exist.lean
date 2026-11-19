-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18_original_fullmark_initial_event_stopped_reward_sources_exist
-- name    : AvramDividend.Classical.avram_ja18_original_fullmark_initial_event_stopped_reward_sources_exist
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T20:34:15.469204+00:00
-- url     : https://prove2.me/theorems/e474d76e-d906-4615-978f-1823f4c1475c
-- title:
--   Original finite-activity full compensated jump stopped cash is centred on all initial-information events
-- statement:
--   Construct, from actual original Standing finite-activity Levy assumptions, source-faithful intrinsic Gaussian R, compensated smallmark Jsmall and full negative mark Jfull, retain exact original ruin-contact terminal and full Stieltjes cash reward, and certify integrability plus vanishing expected full-negative-mark martingale gain on every event in the initial right-continuous filtration. Uses Proved physical two-noise discounted stopped reward and Proved initial-event condExp transfer.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_ubv_jump11_past_event_integral_of_condexp_zero
import Theorems.Thm_AvramDividend_Classical_avram_ja18_original_fullmark_two_noise_discounted_stopped_reward_sources_exist
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18_original_fullmark_initial_event_stopped_reward_sources_exist
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
    let μ : ℝ := ∫ ω, X.X 1 ω ∂P
    ∃ (R Jsmall Jfull : ℝ≥0 → Ω → ℝ),
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Tendsto (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
          atTop (nhds (R t ω))) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Tendsto (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
          atTop (nhds (Jsmall t ω))) ∧
      (∀ t : ℝ≥0, Integrable (R t) P) ∧
      (∀ s t : ℝ≥0, s ≤ t →
        ∀ᵐ ω ∂P, condExp (𝓕.rightCont s) P (R t) ω = R s ω) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Jfull t ω =
          Jsmall t ω + avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω +
          (t : ℝ) * (X.c - μ)) ∧
      Integrable (fun ω => Jfull (τ ω) ω) P ∧
      (∀ᵐ ω ∂P, condExp (𝓕.rightCont 0) P
        (fun ω => Jfull (τ ω) ω) ω = 0) ∧
      (∀ A : Set Ω, MeasurableSet[𝓕.rightCont 0] A →
        (∫ ω in A, Jfull (τ ω) ω ∂P) = 0) ∧
      (∀ᵐ ω ∂P, F ω =
        Real.exp (-(q * (τ ω : ℝ))) *
          w (x + (τ ω : ℝ) * μ + R (τ ω) ω + Jfull (τ ω) ω -
            (if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
             then rightLimit D (τ ω) ω else D (τ ω) ω)) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal) := by sorry
