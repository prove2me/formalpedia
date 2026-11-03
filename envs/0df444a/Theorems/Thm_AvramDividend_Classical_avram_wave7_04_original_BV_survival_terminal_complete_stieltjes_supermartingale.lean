-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_04_original_BV_survival_terminal_complete_stieltjes_supermartingale
-- name    : AvramDividend.Classical.avram_wave7_04_original_BV_survival_terminal_complete_stieltjes_supermartingale
-- status  : Open
-- author  : @WillR
-- created : 2026-11-02T16:17:06.483004+00:00
-- url     : https://prove2.me/theorems/0618723a-bb0b-4fa0-94bc-4def7af7aafa
-- title:
--   Original capped BV stopped supermartingale with survival terminal and complete Stieltjes dividend cash
-- statement:
--   On the original Levy filtered probability space and for every capped admissible dividend strategy, the discounted full Stieltjes cash paid through a deterministic nonnegative horizon plus the expected nonnegative discounted post-rightpayment HJB candidate value on the strict survival event does not exceed its initial value. The full cash includes the time-zero right-payment atom and all continuous dividend mass. The terminal variable is integrable. At ruin or after ruin the terminal reward is zero, and the horizon's own rightpayment atom is included.
-- source:
--   Faithful stopped BV C1 Ito/change-of-variables strengthening of canonical ef7e6c20-a118-46f0-ac94-5b02204bba49, original paper Proposition 4(i) and equation (5.13). Original Omega,P,X, filtration, ruinTime, dividendMeasure and paymentTimes unchanged. Supports a formal parent bridge by nonnegative terminal expectation plus Proved W7-03 original real-budget-to-ENNReal theorem 1c237b6b. Missing proof is the actual stopped source jump compensation and drift generator martingale identity, including Tplus>T right-atom convention, positive cap boundary, ruin overshoot and localisation. The source-specific theorem is intentionally stronger than the parent and independent of parent, avoiding cycles.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_04_original_BV_survival_terminal_complete_stieltjes_supermartingale
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T) :
    let S : ℝ≥0 := ⟨T,hT⟩
    let Term : Ω → ℝ := fun ω =>
      if (S : ℝ≥0∞) < ruinTime X x D ω then
        max 0 (Real.exp (-(q * T)) *
          w (x + X.X S ω - rightLimit D S ω))
      else 0
    Integrable Term P ∧
      (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal ∂P) +
        (∫ ω, Term ω ∂P) ≤ w x := by sorry
