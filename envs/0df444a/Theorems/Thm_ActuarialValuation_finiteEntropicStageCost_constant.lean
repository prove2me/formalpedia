-- Prove2me | Theorems.Thm_ActuarialValuation_finiteEntropicStageCost_constant
-- name    : ActuarialValuation.finiteEntropicStageCost_constant
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T09:38:04.831603+00:00
-- url     : https://prove2.me/theorems/a41615fa-f8c7-4557-b0e5-439dd369fc35
-- title:
--   Deterministic cost and deterministic continuation give their discounted sum
-- statement:
--   When the current action produces exactly the same loss c and the continuation value u in every possible next state, the exponential moment factors into exp(gamma*(c+beta*u)) times unit total probability. Taking the real logarithm and dividing by nonzero gamma recovers the ordinary deterministic discounted amount.
--
--   **Mathematical statement**
--
--   $$
--   Q_{\gamma,\beta}(s,a;F)=c+\beta u
--   $$
-- source:
--   Bäuerle and Glauner (2022), Markov decision processes with recursive risk measures, European Journal of Operational Research 296(3), Definition 4.6, Theorem 4.7, equation (4.2), DOI https://doi.org/10.1016/j.ejor.2021.04.030; Bäuerle and Jaśkiewicz (2024), entropic certainty equivalent, Example 1(a), equation (2), DOI https://doi.org/10.1007/s00186-024-00857-0; derived finite-state discrete-time insurer cost specialisation

import Mathlib
import Definitions.Def_actuarial_finiteEntropicStageCost

namespace ActuarialValuation

theorem finiteEntropicStageCost_constant {S A : Type*} [Fintype S]
  (P : S → A → S → ℝ) (cost : S → A → S → ℝ)
  (beta gamma : ℝ) (next : S → ℝ) (s : S) (a : A) (c u : ℝ)
  (hsum : (∑ t : S, P s a t) = 1)
  (hc : ∀ t, cost s a t = c)
  (hu : ∀ t, next t = u)
  (hgamma : gamma ≠ 0) :
  finiteEntropicStageCost P cost beta gamma next s a = c + beta * u := by sorry

end ActuarialValuation
