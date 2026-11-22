-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_original_finiteactivity_finitecap_trueclock_discounted_G_Jsmall_fullreward_L1
-- name    : AvramDividend.Classical.avram_jump6_original_finiteactivity_finitecap_trueclock_discounted_G_Jsmall_fullreward_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T22:56:58.55959+00:00
-- url     : https://prove2.me/theorems/81e7eba3-9384-422b-8d4d-ed172b23959b
-- title:
--   Exact finite-cap ruin-clipped discounted terminal plus inclusive cash in original Gaussian and compensated smallmark coordinates, with L1 and initial-event measurability
-- statement:
--   For an original Standing finite-negative-activity spectrally negative Lévy process under finite cap, any admissible dividend strategy and physical stopped clock τ, construct an original adapted continuous centred Gaussian process G and a compensated small negative-mark process Jsmall with stopped initial-conditional mean zero. Prove exact pathwise almost-sure equality of the original discounted stopped Term+Cash with the value w of x+τ c+Gτ+Jsmallτ+all original large marks minus the correct right-dividend at strict preruin or non-right dividend at ruin. The original full stopped reward is integrable, cash integrable, terminal strongly measurable and {τ≠0} initially measurable.
-- source:
--   Original exact physical terminal 79a192d2-2e1b-4360-b00c-f802745bebdd (Proved) and allnu finitecap stopped reward L1 bdc679ac-2d2e-4748-a9b4-6369134d673b (Proved). Preflight for original expected budget 15815eff.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_jump6_finiteactivity_true_ruinclipped_terminal_original_continuous_G_and_centered_Jsmall
import Theorems.Thm_AvramDividend_Classical_avram_jump6_original_allnu_finitecap_canonical_stopped_full_reward_L1
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_original_finiteactivity_finitecap_trueclock_discounted_G_Jsmall_fullreward_L1
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
    ∃ (G Jsmall : ℝ≥0 → Ω → ℝ),
      (∀ᵐ ω ∂P, Continuous (fun t : ℝ≥0 => G t ω)) ∧
      (∀ t : ℝ≥0, Integrable (G t) P ∧ (∫ ω, G t ω ∂P) = 0) ∧
      Integrable (fun ω => Jsmall (τ ω) ω) P ∧
      (∀ᵐ ω ∂P, condExp (𝓕.rightCont 0) P
        (fun η => Jsmall (τ η) η) ω = 0) ∧
      AEStronglyMeasurable Term P ∧ Integrable Cash P ∧
      Integrable (fun ω => Term ω + Cash ω) P ∧
      MeasurableSet[𝓕.rightCont 0] {ω : Ω | τ ω ≠ 0} ∧
      (∀ᵐ ω ∂P, Term ω + Cash ω =
        Real.exp (-(q * (τ ω : ℝ))) *
          w (x + (τ ω : ℝ) * X.c +
            G (τ ω) ω + Jsmall (τ ω) ω +
            avram_p4_h_gaussian_intrinsic_large_jump_sum X (τ ω) ω -
            (if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
             then rightLimit D (τ ω) ω else D (τ ω) ω)) + Cash ω) := by sorry
