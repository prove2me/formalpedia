-- Prove2me | Theorems.Thm_FormalizedScopeReach_equal_probabilities
-- name    : FormalizedScopeReach.equal_probabilities
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-15T19:10:58.487476+00:00
-- url     : https://prove2.me/theorems/f11e7b23-e07e-4a98-b94a-81f0c354be8b
-- title:
--   Equal probabilities in the original and two-stage experiments
-- statement:
--   Assume a countable vocabulary, normalized original and outcome-avoiding path laws, and unequal outcome and threshold times almost surely under the original law. The original probability of an outcome before the threshold equals the probability of at least one successful Bernoulli trial in the explicit two-stage experiment on one outcome-free timeline.
-- source:
--   Solo et al., Efficient Generative Prediction for EHR Foundation Models: The SCOPE and REACH Estimators, arXiv:2602.03730v2 (2026), https://arxiv.org/abs/2602.03730v2, Appendix C, Proof of Equal Probabilities

import Definitions.Def_FormalizedScopeReach_Trials

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory

namespace FormalizedScopeReach

theorem equal_probabilities {V : Type} [Countable V] (M : Model V)
    [IsProbabilityMeasure (originalLaw M)] [IsProbabilityMeasure (avoidingLaw M)]
    (hne : ∀ᵐ x ∂originalLaw M, T_O M x ≠ T_E M x) :
    originalLaw M {x | T_O M x < T_E M x} =
      twoStageLaw M 1 {z | true ∈ z.2 0} := by sorry

end FormalizedScopeReach
