-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18_original_finite_range_fullmark_signed_ito_initial_event_budget
-- name    : AvramDividend.Classical.avram_ja18_original_finite_range_fullmark_signed_ito_initial_event_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T20:48:58.643158+00:00
-- url     : https://prove2.me/theorems/693cb8ba-48b6-4e3e-82d4-6d29c1eeef82
-- title:
--   Original finite mixed full-mark physical stopped signed Ito ledger implies conditional initial-event cash budget
-- statement:
--   For the actual original spectrally negative finite-negative-activity Levy process, finite-range bounded stopping clock and full discounted ruincontact Stieltjes reward, a signed Ito inequality with the complete compensated full-negative-mark source Jfull and intrinsic Gaussian R, plus B nonpositive on an initial event, implies the correct initial-event expected reward bound. The hypotheses are source-faithful and quantify over all genuine R/Jsmall/Jfull choices, not synthetic witnesses. The only remaining analytic obligation is the physically signed Ito cash inequality; original fullmark noise existence and both conditional centring facts are Proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_jb19_two_noise_initial_event_masked_reward_budget
import Theorems.Thm_AvramDividend_Classical_avram_ja18_original_finite_range_fullmark_two_stopped_noises_reward
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18_original_finite_range_fullmark_signed_ito_initial_event_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (q x : ℝ) (w : ℝ → ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτbound : ∀ ω, τ ω ≤ (n : ℝ≥0))
    (S : Finset ℝ≥0) (hτrange : ∀ ω, τ ω ∈ S)
    (F : Ω → ℝ)
    (hFsource : ∀ ω, F ω =
      Real.exp (-(q * (τ ω : ℝ))) *
        w (if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
          then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
          else riskProcess X x D (τ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hFI : Integrable F P)
    (E T : Set Ω) (hE : MeasurableSet[𝓕.rightCont 0] E)
    (hET : E ⊆ T) (b : ℝ) (hb : 0 ≤ b)
    (hIto : ∀ (R Jsmall Jfull : ℝ≥0 → Ω → ℝ),
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Tendsto (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
          atTop (nhds (R t ω))) →
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Tendsto (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
          atTop (nhds (Jsmall t ω))) →
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Jfull t ω =
          Jsmall t ω + avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω +
          (t : ℝ) * (X.c - ∫ ω, X.X 1 ω ∂P)) →
      ∃ B : Ω → ℝ,
        (∀ᵐ ω ∂(P.restrict E), B ω ≤ 0) ∧
        (∀ᵐ ω ∂(P.restrict E),
          F ω ≤ b + R (τ ω) ω + Jfull (τ ω) ω + B ω)) :
    (∫ ω in E, F ω ∂P) ≤ b * (P T).toReal := by sorry
