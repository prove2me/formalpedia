-- Prove2me | Theorems.Thm_ActuarialValuation_finiteEntropicStageCost_mono
-- name    : ActuarialValuation.finiteEntropicStageCost_mono
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T09:41:23.166398+00:00
-- url     : https://prove2.me/theorems/79732eef-716b-4c79-8fc7-b4ab95b16ba6
-- title:
--   Entropic stage valuation is monotone in annual and continuation cost
-- statement:
--   Under positive risk aversion and nonnegative discounting, raising any state-contingent annual loss or continuation loss cannot reduce the associated entropic cost. Nonnegative transition weights and their unit sum ensure strictly positive arguments to the monotone logarithm; no extra transition independence is imposed.
--
--   **Mathematical statement**
--
--   $$
--   c_1\le c_2,\ F_1\le F_2\Longrightarrow Q(c_1,F_1)\le Q(c_2,F_2)
--   $$
-- source:
--   Bäuerle and Glauner (2022), Markov decision processes with recursive risk measures, European Journal of Operational Research 296(3), Definition 4.6, Theorem 4.7, equation (4.2), DOI https://doi.org/10.1016/j.ejor.2021.04.030; Bäuerle and Jaśkiewicz (2024), entropic certainty equivalent, Example 1(a), equation (2), DOI https://doi.org/10.1007/s00186-024-00857-0; derived finite-state discrete-time insurer cost specialisation

import Mathlib
import Definitions.Def_actuarial_finiteEntropicStageCost

namespace ActuarialValuation

theorem finiteEntropicStageCost_mono {S A : Type*} [Fintype S]
  (P : S → A → S → ℝ) (cost1 cost2 : S → A → S → ℝ)
  (beta gamma : ℝ) (next1 next2 : S → ℝ) (s : S) (a : A)
  (hP : ∀ t, 0 ≤ P s a t)
  (hsum : (∑ t : S, P s a t) = 1)
  (hbeta : 0 ≤ beta) (hgamma : 0 < gamma)
  (hc : ∀ t, cost1 s a t ≤ cost2 s a t)
  (hnext : ∀ t, next1 t ≤ next2 t) :
  finiteEntropicStageCost P cost1 beta gamma next1 s a ≤
  finiteEntropicStageCost P cost2 beta gamma next2 s a := by sorry

end ActuarialValuation
