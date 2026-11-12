-- Prove2me | Theorems.Thm_FormalizedScopeReach_scope_unbiased
-- name    : FormalizedScopeReach.scope_unbiased
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-15T19:10:38.220342+00:00
-- url     : https://prove2.me/theorems/0ba51344-ba5b-44cf-a777-26faf2ff0d2e
-- title:
--   SCOPE is unbiased
-- statement:
--   Assume a countable vocabulary, the full-history next-token model, almost-sure threshold termination under the original law, and almost surely unequal outcome and threshold times. For every positive sample count, the SCOPE average is integrable and its expectation equals the original probability of an outcome before the threshold. There is no deterministic length bound or finite-mean length assumption.
-- source:
--   Solo et al., Efficient Generative Prediction for EHR Foundation Models: The SCOPE and REACH Estimators, arXiv:2602.03730v2 (2026), https://arxiv.org/abs/2602.03730v2, Section 4.1 and Appendix B

import Definitions.Def_FormalizedScopeReach_Trials

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory

namespace FormalizedScopeReach

theorem scope_unbiased {V : Type} [Countable V] (M : Model V)
    [IsProbabilityMeasure (originalLaw M)]
    (hne : ∀ᵐ x ∂originalLaw M, T_O M x ≠ T_E M x) (n : ℕ) (hn : 0 < n) :
    Integrable (𝒮 M n) (iidLaw (originalLaw M) n) ∧
      (∫ xs, 𝒮 M n xs ∂iidLaw (originalLaw M) n) = targetProbability M := by sorry

end FormalizedScopeReach
