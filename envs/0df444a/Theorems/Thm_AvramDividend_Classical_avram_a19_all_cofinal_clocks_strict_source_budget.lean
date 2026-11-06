-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a19_all_cofinal_clocks_strict_source_budget
-- name    : AvramDividend.Classical.avram_a19_all_cofinal_clocks_strict_source_budget
-- status  : Open
-- author  : @WillR
-- created : 2026-11-06T00:15:26.039648+00:00
-- url     : https://prove2.me/theorems/a233906b-c5fd-4b4f-a1f0-b7ef07c91b8a
-- title:
--   Original BV strict stopped source expectation for every cofinal observation grid
-- statement:
--   For every monotone nonnegative observation sequence strictly cofinal below positive T, establish the source-specific original controlled BV Lévy HJB expected upper bound for strict Stieltjes cash at each observation clock together with the surviving true T terminal. Original generator, gradient, secant, ruin and cap hypotheses are unchanged. This isolates the stochastic estimate from deterministic construction of the clocks.
-- source:
--   Source-exact unresolved stochastic component of b39f2dd1. The independent positive real cofinal-clock existence obligation ef6585cb closes the only deterministic step. No budget from the parent a19d8b28 or its descendants is used.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a19_all_cofinal_clocks_strict_source_budget
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
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T) :
    let S : ℝ≥0 := ⟨T, hT⟩
    ∀ u : ℕ → ℝ, Monotone u →
      (∀ n, 0 ≤ u n) → (∀ n, u n < T) →
      (∀ s : ℝ, s < T → ∃ n, s < u n) →
      (∀ n, (∫ ω,
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (u n),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)).toReal +
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
           Real.exp (-(q * T)) * w (riskProcess X x D S ω)
         else 0) ∂P) ≤ w x) := by sorry
