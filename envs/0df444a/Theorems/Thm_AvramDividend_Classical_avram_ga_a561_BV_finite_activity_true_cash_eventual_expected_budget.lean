-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a561_BV_finite_activity_true_cash_eventual_expected_budget
-- name    : AvramDividend.Classical.avram_ga_a561_BV_finite_activity_true_cash_eventual_expected_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T08:49:39.559207+00:00
-- url     : https://prove2.me/theorems/861f0677-9349-4fe4-bb17-bcf216877333
-- title:
--   True finite-activity BV top-cap stopped cash has integrability and an eventual HJB mean budget
-- statement:
--   Under the original finite negative-jump activity and top-cap HJB supersolution, each true stopped discounted paid-cash plus survival terminal-value random variable is integrable, and for every positive epsilon the expected value at all sufficiently fine terminal-strip cutoffs is at most w(x)+epsilon.
-- source:
--   Original finite-activity stopped cash compensation, finite-jump strip and HJB generator inequality; bvb59 proves a conditional version when intensity is positive.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a561_BV_finite_activity_true_cash_eventual_expected_budget
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
    (T : ℝ) (hT : 0 < T)
    (hTop : C = ⊤)
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let F : ℕ → Ω → ℝ := fun n ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (riskProcess X x D S ω)
        else 0)
    (∀ n, Integrable (F n) P) ∧
    (∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in (atTop : Filter ℕ), (∫ ω, F n ω ∂P) ≤ w x + ε) := by sorry
