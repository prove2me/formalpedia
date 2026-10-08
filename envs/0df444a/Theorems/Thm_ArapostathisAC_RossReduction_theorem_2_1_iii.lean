-- Prove2me | Theorems.Thm_ArapostathisAC_RossReduction_theorem_2_1_iii
-- name    : ArapostathisAC.RossReduction.theorem_2_1_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T15:07:36.594134+00:00
-- url     : https://prove2.me/theorems/cab69fcc-11aa-44e4-a988-45375fdf2c8a
-- title:
--   Theorem 2.1(iii): a stationary deterministic discount-optimal policy exists
-- statement:
--   For a countable-state controlled Markov process with the compactness and continuity assumptions of §5 and nonnegative cost, and every discount factor $0<\beta<1$, there is an admissible stationary deterministic policy $f$ such that
--
--   $$J_\beta(i,f)=J_\beta^*(i)\qquad\text{for every }i\in S.$$
--
--   This existence result supplies a policy for the transformed discounted problem in Theorem 5.6.
--
--   **Formalization Note** The §5 compactness and coordinatewise continuity assumptions are fields of the model. The optimal value takes the infimum over all history-dependent randomized admissible policies. The theorem itself does not require bounded cost, although bounded cost is assumed in the later application to Theorem 5.6.
-- source:
--   Arapostathis et al., Discrete-time controlled Markov processes with average cost criterion: a survey, SIAM J. Control Optim. 31(2) (1993), p. 289, Theorem 2.1(iii), specialized to §5.1 p. 301; https://doi.org/10.1137/0331018

import Mathlib
import Definitions.Def_ArapostathisAC_RossReduction_CMP

namespace ArapostathisAC.RossReduction

/-- Theorem 2.1(iii), specialized to the countable-state §5 model. -/
theorem theorem_2_1_iii {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]
    (M : CMP A) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ f : ℕ → A, DiscountOptimalFor M β f := by sorry

end ArapostathisAC.RossReduction
