-- Prove2me | Theorems.Thm_FormalizedScopeReach_reach_raoBlackwell
-- name    : FormalizedScopeReach.reach_raoBlackwell
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-15T19:11:25.103372+00:00
-- url     : https://prove2.me/theorems/65420518-5d7e-460c-bfa6-a002f74f8c6f
-- title:
--   REACH is a Rao–Blackwellization
-- statement:
--   For any countable vocabulary and normalized outcome-avoiding path law, take any positive number of independent outcome-free timelines and sample their conditionally independent Bernoulli trials using original next-token hazards. The REACH average, viewed on this joint space, equals almost surely the conditional expectation of the trial-success indicator average given the complete indexed pool of outcome-free timelines. The theorem uses Mathlib conditional expectation.
-- source:
--   Solo et al., Efficient Generative Prediction for EHR Foundation Models: The SCOPE and REACH Estimators, arXiv:2602.03730v2 (2026), https://arxiv.org/abs/2602.03730v2, Appendix Q

import Definitions.Def_FormalizedScopeReach_Trials

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory

namespace FormalizedScopeReach

theorem reach_raoBlackwell {V : Type} [Countable V] (M : Model V)
    [IsProbabilityMeasure (avoidingLaw M)] (n : ℕ) (hn : 0 < n) :
    (fun z : (Fin n → Timeline V) × (Fin n → List Bool) => ℛ M n z.1) =ᵐ[twoStageLaw M n]
      (twoStageLaw M n)[trialMean n | timelineInformation n] := by sorry

end FormalizedScopeReach
