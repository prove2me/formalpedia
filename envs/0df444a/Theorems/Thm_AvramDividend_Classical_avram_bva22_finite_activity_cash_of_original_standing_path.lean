-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva22_finite_activity_cash_of_original_standing_path
-- name    : AvramDividend.Classical.avram_bva22_finite_activity_cash_of_original_standing_path
-- status  : Open
-- author  : @WillR
-- created : 2026-11-11T00:46:53.777645+00:00
-- url     : https://prove2.me/theorems/525fbbf3-62b2-405b-bf31-c8ba7753f1f2
-- title:
--   Finite-activity original BV cash budget from exact same-space standing path decomposition
-- statement:
--   Source exact finite-activity branch of the original complement dividend cash bound: assume the genuine BV physical drift-minus-source negative jumps identity on the single original probability space up to the horizon. Prove expected discounted closed-horizon Stieltjes dividend cash at most w(x), retaining the real predictable jump, time-zero payment, ruin and horizon atom accounting. This is the irreducible cash-Stieltjes/compensator step after the path decomposition.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_bva22_finite_activity_cash_of_original_standing_path
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
    (T : ℝ) (hT : 0 ≤ T)
    (hEnvelope : ¬ (x + T * X.drift ≤ w x))
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤)
    (hTpos : 0 < T)
    (hSource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      t ≤ (⟨T, le_of_lt hTpos⟩ : ℝ≥0) →
      (t : ℝ) * X.drift - X.X t ω =
        (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0)) :
    (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal ∂P) ≤
      w x := by sorry
