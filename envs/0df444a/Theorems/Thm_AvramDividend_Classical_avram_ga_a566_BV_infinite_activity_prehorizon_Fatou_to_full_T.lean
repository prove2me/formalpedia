-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a566_BV_infinite_activity_prehorizon_Fatou_to_full_T
-- name    : AvramDividend.Classical.avram_ga_a566_BV_infinite_activity_prehorizon_Fatou_to_full_T
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T10:02:28.261196+00:00
-- url     : https://prove2.me/theorems/3278841c-8710-4367-92c9-21e79c64febe
-- title:
--   Infinite-activity BV prehorizon supermartingale budgets imply the true finite-cap terminal expectation
-- statement:
--   For the exact bounded-variation infinite-negative-jump-activity finite-cap HJB dividend strategy, assume every strictly preterminal stopped original discounted cash plus its actual survivor reward has nonnegative lintegral bounded by w(x). Then two-stage Fatou and strict real-cash cutoff convergence establish the original full-T strict-cash-plus-survivor-terminal expected bound. This separates the hard stochastic preterminal budget from the measure-theoretic terminal transfer.
-- source:
--   Prove2Me a62 prehorizon stochastic supermartingale budget; proved a63 strict prehorizon Fatou and p3 grid4 strict terminal convergence; twice-applied Fatou a565.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a566_BV_infinite_activity_prehorizon_Fatou_to_full_T
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
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T)
    (hFinite : C ≠ ⊤)
    (hactivity : ¬ X.ν (Iio (0 : ℝ)) < ⊤)
    (hPre : ∀ (r : ℝ≥0), 0 < r → (r : ℝ) < T →
      (∫⁻ ω, ENNReal.ofReal
        ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (r : ℝ),
            ENNReal.ofReal (Real.exp (-(q * t)))
              ∂(dividendMeasure D ω)).toReal +
         (if (r : ℝ≥0∞) < ruinTime X x D ω then
            Real.exp (-(q * (r : ℝ))) * w (riskProcess X x D r ω)
          else 0)) ∂P) ≤ ENNReal.ofReal (w x)) :
    let S : ℝ≥0 := ⟨T, hT⟩
    (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal +
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (riskProcess X x D S ω)
         else 0) ∂P) ≤ w x := by sorry
