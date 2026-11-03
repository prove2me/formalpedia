-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_actual_stopped_HJB_cash_budget
-- name    : AvramDividend.Classical.avram_wave7_08_source_actual_stopped_HJB_cash_budget
-- status  : Open
-- author  : @WillR
-- created : 2026-11-02T14:33:47.270209+00:00
-- url     : https://prove2.me/theorems/447f725b-9c4e-4272-9e22-e8f10fa2598b
-- title:
--   True original ruin-stopped source HJB cash budget at exact capped real clock
-- statement:
--   The original-source mixed Gaussian and compensated negative-jump stopped Ito-Meyer expected Stieltjes cash estimate at the exact pathwise real clock τ=(min(ruinTime,n)).toNNReal, retaining Ω,P,X,D, corrected w(0)>=0 and positive reserve. The Proved conditional W6-06 theorem 8cd5e123 supplies the final inequality once source stopped martingale and drift hypotheses are established.
-- source:
--   Exact W7-08 remaining stochastic cutset after Proved original stopped cash inclusion 798c835a and bounded clock conversion 6b7a13a0, without altered model or cash measure.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_08_source_actual_stopped_HJB_cash_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
      Iic (((min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal : ℝ≥0) : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by sorry
