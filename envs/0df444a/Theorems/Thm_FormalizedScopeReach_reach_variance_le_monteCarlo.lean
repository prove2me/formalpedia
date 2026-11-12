-- Prove2me | Theorems.Thm_FormalizedScopeReach_reach_variance_le_monteCarlo
-- name    : FormalizedScopeReach.reach_variance_le_monteCarlo
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-15T19:11:43.197924+00:00
-- url     : https://prove2.me/theorems/1f10f803-adf2-46b0-a4c3-d72eb10a409e
-- title:
--   REACH variance is at most Monte Carlo variance
-- statement:
--   Assume a countable vocabulary, normalized original and outcome-avoiding laws, and almost surely unequal outcome and threshold times under the original law. For every positive common sample count, REACH under independent outcome-avoiding sampling and the Monte Carlo estimator under independent original sampling both have finite second moments. The variance of REACH is less than or equal to the variance of Monte Carlo. The actual threshold is retained, and no bound or finite expectation is imposed on the number of tokens.
-- source:
--   Solo et al., Efficient Generative Prediction for EHR Foundation Models: The SCOPE and REACH Estimators, arXiv:2602.03730v2 (2026), https://arxiv.org/abs/2602.03730v2, Section 4.4, equation (1)

import Definitions.Def_FormalizedScopeReach_Trials

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory

namespace FormalizedScopeReach

theorem reach_variance_le_monteCarlo {V : Type} [Countable V] (M : Model V)
    [IsProbabilityMeasure (originalLaw M)] [IsProbabilityMeasure (avoidingLaw M)]
    (hne : ∀ᵐ x ∂originalLaw M, T_O M x ≠ T_E M x) (n : ℕ) (hn : 0 < n) :
    MemLp (ℛ M n) 2 (iidLaw (avoidingLaw M) n) ∧
    MemLp (M₀ M n) 2 (iidLaw (originalLaw M) n) ∧
      variance (ℛ M n) (iidLaw (avoidingLaw M) n) ≤
        variance (M₀ M n) (iidLaw (originalLaw M) n) := by sorry

end FormalizedScopeReach
