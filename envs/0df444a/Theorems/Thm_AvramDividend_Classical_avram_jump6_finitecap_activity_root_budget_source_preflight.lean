-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_finitecap_activity_root_budget_source_preflight
-- name    : AvramDividend.Classical.avram_jump6_finitecap_activity_root_budget_source_preflight
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T18:52:37.057539+00:00
-- url     : https://prove2.me/theorems/574fad72-dbbc-4bf9-89e2-79bdd2e6746e
-- title:
--   Finite-activity finite-cap original stopped Itô source preflight: σ positive, L1 terminal and HJB dividend jump
-- statement:
--   Under the exact original finite-activity, unbounded-variation, HJB and admissible dividend hypotheses of the root-connected expected budget, if the cap is finite then the Gaussian coefficient is strictly positive; the true ruin-clipped clock is bounded by k; the stopped post-dividend terminal is integrable and almost-everywhere strongly measurable; the exact physical stopped Term+Cash is integrable; and the canonical right-dividend drop inequality holds for all zero and pre-ruin times. All claims are proved from currently Proved original source theorems, leaving only the stopped Itô–Meyer expectation inequality as the genuine outstanding budget.
-- source:
--   Root-connected original positive-clock finite-activity expected budget 15815eff-2c54-41e3-97a6-d216a3efb8d8; Proved antecedents 544833a4-bb18-4e96-b4ff-cef18c8806cd, edebe535-25e3-417c-84fb-5a8a21a57b8a, 87d29cce-b557-4e47-8b59-ca35f657cc3b, 9dbbf2f2-bd98-4414-bc95-b3dc25e270b2.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_finiteactivity_UBV_gaussian_sigma_positive
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_subordinate_clock_bounded_by_horizon_and_ruin
import Theorems.Thm_AvramDividend_Classical_avram_jump6_finitecap_original_stopped_reward_integrable
import Theorems.Thm_AvramDividend_Classical_avram_jump6_original_ubv_hjb_implies_right_dividend_secant
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_finitecap_activity_root_budget_source_preflight
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hxpos : 0 < x)
    (k : ℕ) (hk : 0 < k)
    (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (k : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω = if τ ω = 0 ∨
      (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω = (∫⁻ s in
      paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hCashI : Integrable Cash P)
    (hFiniteCap : C ≠ ⊤) :
    (0 < X.σ) ∧
    (∀ ω, τ ω ≤ (k : ℝ≥0)) ∧
    Integrable Term P ∧
    AEStronglyMeasurable Term P ∧
    Integrable (fun ω => Term ω + Cash ω) P ∧
    (∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω))) := by sorry
