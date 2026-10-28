-- Prove2me | Theorems.Thm_AvramDividend_Classical_local_verification_separated_countable_jump_drop_budget
-- name    : AvramDividend.Classical.local_verification_separated_countable_jump_drop_budget
-- status  : Disproved
-- author  : @WillR
-- created : 2026-10-22T22:24:39.068021+00:00
-- url     : https://prove2.me/theorems/91f4781b-1386-467f-9bb1-720d169ab082
-- title:
--   Missing pathwise upper bound on countably many discounted verification-value drops
-- statement:
--   Explicitly isolated UNPROVED implication required by local_verification_separated_countable_dividend_budget: for an admissible Lévy-controlled dividend path, the countable sum of discounted drops of a verification function at dividend times does not exceed the initial value. Caution: this is a pathwise statement, unlike the usual HJB stochastic verification inequality in expectation, and may be FALSE without further hypotheses preventing favourable Lévy increments. Publication isolates the mathematical validity question; it is not evidence of a proof. If false the parent needs a corrected expected-value conclusion.
-- source:
--   Original parent e71b6299-f107-47fe-940c-d9930dca2985 and Proved eec96fd3-367d-43a5-bebe-35bb387a0809; required missing implication between their conclusions. Check pathwise stochastic counterexamples before attempting a full proof.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.local_verification_separated_countable_jump_drop_budget
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
    (∑' s : S, ENNReal.ofReal (Real.exp (-(q * (s : ℝ))) *
      (w (riskProcess X x D (s : ℝ).toNNReal ω) -
       w (riskProcess X x D (s : ℝ).toNNReal ω -
         (rightLimit D (s : ℝ).toNNReal ω - D (s : ℝ).toNNReal ω))))) ≤
      ENNReal.ofReal (w x) := by sorry
