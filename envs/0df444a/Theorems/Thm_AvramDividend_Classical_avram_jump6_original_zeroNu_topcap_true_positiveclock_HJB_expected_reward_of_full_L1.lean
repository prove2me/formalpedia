-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_original_zeroNu_topcap_true_positiveclock_HJB_expected_reward_of_full_L1
-- name    : AvramDividend.Classical.avram_jump6_original_zeroNu_topcap_true_positiveclock_HJB_expected_reward_of_full_L1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T23:20:49.249287+00:00
-- url     : https://prove2.me/theorems/2421ca1b-61fb-49cf-abe5-b75feb073173
-- title:
--   Original Gaussian-only infinite-cap true stopped dividend reward positive-clock expected HJB bound, provided exact stopped payoff L1
-- statement:
--   For the original spectrally negative Standing unbounded-variation Lévy process with exactly zero negative Lévy measure, its pure Gaussian infinite-cap dividend problem, full positive-reserve HJB hypotheses and original dividend strategy, prove the original event-restricted expectation of the *exact* ruin-clipped discounted post-right-dividend terminal plus inclusive Stieltjes cash is bounded by w(x) times the true positive-clock probability. Require only the independent unbounded-cap L1 of that actual reward; derive Gaussian nonzero, initial-event measurability and the stopped Gaussian Ito source bound from existing Proved original theorems.
-- source:
--   Proved original Gaussian stopped Ito–Meyer topcap 249c532d-4ec0-498c-81f0-b380dd476344, Proved 37d963a0 positive sigma, Proved 48783265 stopped meas and cash L1, Proved bce62e25 timezero positive-clock measurable. Root positive-clock expected budget 15815eff still needs topcap L1 and nonzero jump activity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_zero_levy_ubv_sigma_pos
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_gaussian_masked_expected_topcap
import Theorems.Thm_AvramDividend_Classical_avram_jump6_original_canonical_true_stopped_reward_measurable_Cash_integrable
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite12_positive_clock_initial_measurable
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_jump6_original_zeroNu_topcap_true_positiveclock_HJB_expected_reward_of_full_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hNuZero : X.ν = 0)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hTop : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
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
      Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hRewardI : Integrable (fun ω => Term ω + Cash ω) P) :
    MeasurableSet[𝓕.rightCont 0] {ω : Ω | τ ω ≠ 0} ∧
      (∫ ω in {η : Ω | τ η ≠ 0}, Term ω + Cash ω ∂P) ≤
        w x * (P {η : Ω | τ η ≠ 0}).toReal := by sorry
