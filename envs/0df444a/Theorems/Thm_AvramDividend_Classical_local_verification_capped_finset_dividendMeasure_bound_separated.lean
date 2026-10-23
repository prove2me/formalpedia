-- Prove2me | Theorems.Thm_AvramDividend_Classical_local_verification_capped_finset_dividendMeasure_bound_separated
-- name    : AvramDividend.Classical.local_verification_capped_finset_dividendMeasure_bound_separated
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T03:08:23.794337+00:00
-- url     : https://prove2.me/theorems/05bef5a0-76bc-472a-91f9-17ccbb8a9ed0
-- title:
--   The discounted dividend measure on a finite set of active payment times is bounded by the sum of the discounted verification-value drops, under the two separate generator and gradient inequalities
-- statement:
--   The finite-set discounted dividend-measure bound stated with the two separate analytic hypotheses on the verification function, namely the nonpositive generator drift X.generator w y - q * w y ≤ 0 and the unit lower bound on the gradient 1 ≤ deriv w y, in place of the single HJB equality max (X.generator w y - q * w y) (1 - deriv w y) = 0. The Proved lemma local_verification_capped_finset_dividendMeasure_bound assumes the HJB equality, and the two separate inequalities only imply that this maximum is nonpositive, not that it vanishes, so the HJB form does not follow from them. This variant is the finite budget needed to discharge the countable budget local_verification_separated_countable_dividend_budget, which bounds the discounted dividend measure on a countable set of active payment times by the initial verification value w x: the countable budget is obtained by applying the finite budget to the finitely many jump times below each index of an enumeration of the countable set and then passing to the limit, and that passage needs the finite budget in the separated form. The proof proceeds by the same atom-by-atom comparison as the Proved lemma: the atom mass of the Lebesgue-Stieltjes measure at a time s is the right jump of D there, and the right jump is bounded by the drop of the verification value across that jump, which the two separate inequalities control.
-- source:
--   The separated-hypothesis variant of the Proved theorem local_verification_capped_finset_dividendMeasure_bound, which assumes the HJB equality max (X.generator w y - q * w y) (1 - deriv w y) = 0. The two separate inequalities X.generator w y - q * w y ≤ 0 and 1 ≤ deriv w y imply only that the maximum is nonpositive, so the HJB form is not available to the target local_verification_separated_countable_dividend_budget, whose hypotheses are the separate ones. That target is the countable budget of the local verification argument, and its proof applies the finite budget to the finitely many jump times below each index of an enumeration of the countable set of active payment times and then passes to the limit, so it needs this finite budget in the separated form. This is the finite counterpart of the Proved theorem local_verification_capped_countable_dividendMeasure_bound_separated, which gives the same comparison on a countable set of times.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.local_verification_capped_finset_dividendMeasure_bound_separated
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
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hxC : ENNReal.ofReal x ≤ C)
    (ω : Ω) (S : Finset ℝ)
    (hNonneg : ∀ s ∈ S, 0 ≤ s)
    (hActive : ∀ s ∈ S,
      s.toNNReal = 0 ∨ (s.toNNReal : ℝ≥0∞) < ruinTime X x D ω) :
    (∫⁻ s in (S : Set ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ≤
    ∑ s ∈ S, ENNReal.ofReal (Real.exp (-(q * s)) *
      (w (riskProcess X x D s.toNNReal ω) -
        w (riskProcess X x D s.toNNReal ω -
          (rightLimit D s.toNNReal ω - D s.toNNReal ω)))) := by sorry
