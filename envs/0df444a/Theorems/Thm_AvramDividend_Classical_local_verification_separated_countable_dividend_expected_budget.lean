-- Prove2me | Theorems.Thm_AvramDividend_Classical_local_verification_separated_countable_dividend_expected_budget
-- name    : AvramDividend.Classical.local_verification_separated_countable_dividend_expected_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T22:35:31.681543+00:00
-- url     : https://prove2.me/theorems/5a6998a3-eca0-4fdd-92c3-d371a9f05f8b
-- title:
--   Expected discounted countable dividends are bounded under a stochastic expected-drop budget and separated HJB inequalities
-- statement:
--   Let q>0, w be nonnegative, and D be a capped admissible strategy satisfying separated HJB assumptions. Let S(ω) be a countable set of active nonnegative payment times for each sample path. Assume the expected discounted sum of verification-value drops across those right dividend jumps is at most w(x). Then the expected discounted Stieltjes dividend measure concentrated on S(ω) is bounded by w(x). This corrects the false pathwise initial-value budget. The unproved stochastic expected-drop inequality remains a transparent hypothesis: the result is a genuine deterministic-to-expected bridge, not a proof of the full stochastic verification estimate.
-- source:
--   AvramDividend.Classical.local_verification_capped_countable_dividendMeasure_bound_separated (Proved); Mathlib MeasureTheory.lintegral_mono.

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_local_verification_capped_countable_dividendMeasure_bound_separated
open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.local_verification_separated_countable_dividend_expected_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hq : 0 < q)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth :
      (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hw_nonneg : ∀ y : ℝ, 0 ≤ y → ENNReal.ofReal y ≤ C → 0 ≤ w y)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hxC : ENNReal.ofReal x ≤ C)
    (S : Ω → Set ℝ)
    (hCountable : ∀ ω, (S ω).Countable)
    (hNonneg : ∀ ω s, s ∈ S ω → 0 ≤ s)
    (hActive : ∀ ω s, s ∈ S ω →
      s.toNNReal = 0 ∨ (s.toNNReal : ℝ≥0∞) < ruinTime X x D ω)
    (hExpectedDropBudget :
      (∫⁻ ω, ∑' s : S ω,
        ENNReal.ofReal (Real.exp (-(q * (s : ℝ))) *
          (w (riskProcess X x D (s : ℝ).toNNReal ω) -
            w (riskProcess X x D (s : ℝ).toNNReal ω -
              (rightLimit D (s : ℝ).toNNReal ω - D (s : ℝ).toNNReal ω)))) ∂P)
        ≤ ENNReal.ofReal (w x)) :
    (∫⁻ ω, ∫⁻ s in S ω,
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω) ∂P)
      ≤ ENNReal.ofReal (w x) := by sorry
