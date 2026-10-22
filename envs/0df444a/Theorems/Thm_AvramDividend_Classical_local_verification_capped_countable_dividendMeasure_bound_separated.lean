-- Prove2me | Theorems.Thm_AvramDividend_Classical_local_verification_capped_countable_dividendMeasure_bound_separated
-- name    : AvramDividend.Classical.local_verification_capped_countable_dividendMeasure_bound_separated
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T11:13:58.13381+00:00
-- url     : https://prove2.me/theorems/eec96fd3-367d-43a5-bebe-35bb387a0809
-- title:
--   The discounted dividend measure on a countable set of active payment times is bounded by the countable sum of the verification-value drops, under the two separate generator and gradient inequalities
-- statement:
--   The countable discounted dividend-measure bound stated with the two separate analytic hypotheses on the verification function, namely the nonpositive generator drift X.generator w y - q * w y ≤ 0 and the unit lower bound on the gradient 1 ≤ deriv w y, in place of the single HJB equality max (X.generator w y - q * w y) (1 - deriv w y) = 0. The Proved lemma local_verification_capped_countable_dividendMeasure_bound assumes the HJB equality, and the two separate inequalities only imply that this maximum is nonpositive, not that it vanishes, so the HJB form does not follow from them. This variant is the statement needed by the bounded-variation stochastic core admissible_cap_truncated_bv_stochastic_core, whose hypotheses are exactly the two separate inequalities. The proof proceeds by the same atom-by-atom comparison: the atom mass of the Lebesgue-Stieltjes measure at a time s is the right jump of D there, and the right jump is bounded by the drop of the verification value across that jump, which the two separate inequalities control.
-- source:
--   The separated-hypothesis variant of the Proved theorem local_verification_capped_countable_dividendMeasure_bound, which assumes the HJB equality max (X.generator w y - q * w y) (1 - deriv w y) = 0. The two separate inequalities X.generator w y - q * w y ≤ 0 and 1 ≤ deriv w y imply only that the maximum is nonpositive, so the HJB form is not available to the target admissible_cap_truncated_bv_stochastic_core, whose hypotheses are the separate ones. This is the countable discounted dividend-measure bound needed to discharge that target.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.local_verification_capped_countable_dividendMeasure_bound_separated
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
    (ω : Ω) (S : Set ℝ) (hCountable : S.Countable)
    (hNonneg : ∀ s ∈ S, 0 ≤ s)
    (hActive : ∀ s ∈ S,
      s.toNNReal = 0 ∨ (s.toNNReal : ℝ≥0∞) < ruinTime X x D ω) :
    (∫⁻ s in S,
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ≤
    ∑' s : S, ENNReal.ofReal (Real.exp (-(q * (s : ℝ))) *
      (w (riskProcess X x D (s : ℝ).toNNReal ω) -
        w (riskProcess X x D (s : ℝ).toNNReal ω -
          (rightLimit D (s : ℝ).toNNReal ω - D (s : ℝ).toNNReal ω)))) := by sorry
