-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_actual_positive_clock_finitecap_full_reward_with_same_initially_centered_G_J
-- name    : AvramDividend.Classical.avram_jump6_actual_positive_clock_finitecap_full_reward_with_same_initially_centered_G_J
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T23:14:26.88547+00:00
-- url     : https://prove2.me/theorems/7ebc1319-992f-452f-be65-9007081092f9
-- title:
--   Exact finitecap positive-clock source stopped reward with the same original Gaussian and smallmark channels, both eventwise centred
-- statement:
--   For the original finite-activity Standing spectrally negative Lévy process and any admissible strategy D, finite cap C, positive horizon n, and the exact original ruin-clipped stopping clock τ, construct one pair of physical Gaussian G and compensated small negative-jump Jsmall source processes. Prove at the actual event A={τ≠0} both stopped integrals are integrable and have expected value zero, A is measurable at time zero, the original discounted terminal plus inclusive physical dividend cash is L1, and its actual nonlinear terminal is the exact original function w applied to x+τ c+Gτ+Jsmallτ+original large marks minus precisely the correct pre/at-ruin dividend payments. No independent Gaussian/jump witnesses or expected reward upper bound assumptions.
-- source:
--   Proved 20115e40, bdc679ac, 1c983d3d, 85c316b5. Missing true nonlinear stopped Ito-Meyer expected source budget 15815eff and root 545c65ef.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_jump6_original_bounded_clock_continuous_gaussian_smallmark_both_eventwise_centered
import Theorems.Thm_AvramDividend_Classical_avram_jump6_original_allnu_finitecap_canonical_stopped_full_reward_L1
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_all_stopped_clocks_le_integer_horizon
import Theorems.Thm_AvramDividend_Classical_avram_ja18_original_ruinclipped_stopped_reserve_full_threechannel_source
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_actual_positive_clock_finitecap_full_reward_with_same_initially_centered_G_J
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (x : ℝ) (C : ℝ≥0∞) (hCfinite : C ≠ ⊤)
    (hxc : ENNReal.ofReal x ≤ C)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 < q)
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω =
      Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) :
    let A : Set Ω := {ω | τ ω ≠ 0}
    ∃ (G Jsmall : ℝ≥0 → Ω → ℝ),
      MeasurableSet[𝓕.rightCont 0] A ∧
      Integrable (fun ω => Term ω + Cash ω) P ∧
      Integrable (fun ω => G (τ ω) ω) P ∧
      Integrable (fun ω => Jsmall (τ ω) ω) P ∧
      (∫ ω in A, G (τ ω) ω ∂P) = 0 ∧
      (∫ ω in A, Jsmall (τ ω) ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, Term ω + Cash ω =
        Real.exp (-(q * (τ ω : ℝ))) *
          w (x + (τ ω : ℝ) * X.c +
            G (τ ω) ω + Jsmall (τ ω) ω +
            avram_p4_h_gaussian_intrinsic_large_jump_sum X (τ ω) ω -
            (if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
             then rightLimit D (τ ω) ω else D (τ ω) ω)) + Cash ω) := by sorry
