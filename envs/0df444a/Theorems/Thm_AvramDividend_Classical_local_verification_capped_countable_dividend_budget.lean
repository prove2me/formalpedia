-- Prove2me | Theorems.Thm_AvramDividend_Classical_local_verification_capped_countable_dividend_budget
-- name    : AvramDividend.Classical.local_verification_capped_countable_dividend_budget
-- status  : Open
-- author  : @WillR
-- created : 2026-10-21T08:15:36.037705+00:00
-- url     : https://prove2.me/theorems/6ad36efb-f484-4d33-803e-f49a3c8ff89f
-- title:
--   The discounted dividends paid at a countable set of times are bounded by the initial verification value, for an admissible strategy
-- statement:
--   Let X be a spectrally negative Levy process with the standing assumptions, let q > 0, and let w be a candidate satisfying the HJB system on the admissible range, that is the generator residual is nonpositive and the derivative is at least one. Let D be an admissible dividend strategy whose reserve never exceeds the cap C, and let S be a countable set of times at which the strategy is still active. Then the expected discounted dividend paid at the times of S, measured with the Lebesgue-Stieltjes measure of the strategy, is bounded by the initial verification value w(x). This is the countable counterpart of the finite HJB budget, in which the discounted dividends paid at finitely many successive times sum to at most w(x) because the reserve decreases by exactly the dividend paid and the drop of w dominates the dividend. It is the step that turns the finite budget into the bound for the discounted dividend measure, and hence into the local verification theorem of Proposition 4(i) of Avram, Palmowski and Pistorius (2007).
-- source:
--   The countable version of the finite HJB budget of Proposition 4(i) in Avram, Palmowski and Pistorius (2007), Section 5.4. The finite budget is the Proved theorem local_verification_hjb_discounted_finite_dividend_bound, the pathwise countable comparison with the drop of the verification function is the Proved theorem local_verification_capped_countable_dividendMeasure_bound, and the countable support of the jumps of the strategy is the Proved theorem dividendStrategy_rightJump_support_countable. Formalised in the Avram Dividend Classical proof programme.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.local_verification_capped_countable_dividend_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth :
      (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hxC : ENNReal.ofReal x ≤ C)
    (ω : Ω) (S : Set ℝ) (hCountable : S.Countable)
    (hNonneg : ∀ s ∈ S, 0 ≤ s)
    (hActive : ∀ s ∈ S,
      s.toNNReal = 0 ∨ (s.toNNReal : ℝ≥0∞) < ruinTime X x D ω) :
    (∫⁻ s in S, ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ≤
      ENNReal.ofReal (w x) := by sorry
