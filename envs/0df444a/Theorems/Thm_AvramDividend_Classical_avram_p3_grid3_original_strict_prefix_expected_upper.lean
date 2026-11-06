-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_strict_prefix_expected_upper
-- name    : AvramDividend.Classical.avram_p3_grid3_original_strict_prefix_expected_upper
-- status  : Open
-- author  : @WillR
-- created : 2026-11-06T00:19:17.319728+00:00
-- url     : https://prove2.me/theorems/d7196ee6-bb23-4f23-a53b-825852a6a759
-- title:
--   Original BV strict cash-prefix and surviving prepayment terminal have expected upper budget at every finite horizon
-- statement:
--   An exact original-process discounted strict dividendMeasure cash prefix ending at T−δ(n), together with the surviving original pre-rightpayment terminal value at T, has expectation at most w(x), under the canonical original bounded-variation Standing/C1/HJB/admissibility and right-payment secant assumptions. The margin δ is positive and ≤T, and no surrogate process or global regularity across ruin is assumed. This single scalar bound is the remaining hard source for the signed Fatou certificate after the accepted GRID4 integrability/liminf theorem and the explicit signed-witness adapter.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid3_original_strict_prefix_expected_upper
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
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
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T)
    (δ : ℕ → ℝ) (hδpos : ∀ n, 0 < δ n)
    (hδle : ∀ n, δ n ≤ T) :
    let S : ℝ≥0 := ⟨T, hT⟩
    let F : ℕ → Ω → ℝ := fun n ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω)
      else 0)
    ∀ n, (∫ ω, F n ω ∂P) ≤ w x := by sorry
