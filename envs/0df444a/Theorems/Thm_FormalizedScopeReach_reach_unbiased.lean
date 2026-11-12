-- Prove2me | Theorems.Thm_FormalizedScopeReach_reach_unbiased
-- name    : FormalizedScopeReach.reach_unbiased
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-15T19:11:10.530584+00:00
-- url     : https://prove2.me/theorems/e9d99b93-75b8-4420-b0ab-e765f4eb5786
-- title:
--   REACH is unbiased
-- statement:
--   Assume a countable vocabulary, normalized original and outcome-avoiding path laws, and unequal outcome and threshold times almost surely under the original law. For every positive sample count, the REACH average under independent outcome-avoiding sampling is integrable and has expectation equal to the original probability of an outcome before the threshold. Neither path law is required to have bounded lengths or finite expected length.
-- source:
--   Solo et al., Efficient Generative Prediction for EHR Foundation Models: The SCOPE and REACH Estimators, arXiv:2602.03730v2 (2026), https://arxiv.org/abs/2602.03730v2, Section 4.3 and Appendix C

import Definitions.Def_FormalizedScopeReach_Trials

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory

namespace FormalizedScopeReach

theorem reach_unbiased {V : Type} [Countable V] (M : Model V)
    [IsProbabilityMeasure (originalLaw M)] [IsProbabilityMeasure (avoidingLaw M)]
    (hne : ∀ᵐ x ∂originalLaw M, T_O M x ≠ T_E M x) (n : ℕ) (hn : 0 < n) :
    Integrable (ℛ M n) (iidLaw (avoidingLaw M) n) ∧
      (∫ xs, ℛ M n xs ∂iidLaw (avoidingLaw M) n) = targetProbability M := by sorry

end FormalizedScopeReach
