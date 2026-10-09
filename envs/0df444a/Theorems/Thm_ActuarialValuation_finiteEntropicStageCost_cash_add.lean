-- Prove2me | Theorems.Thm_ActuarialValuation_finiteEntropicStageCost_cash_add
-- name    : ActuarialValuation.finiteEntropicStageCost_cash_add
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T09:42:19.359213+00:00
-- url     : https://prove2.me/theorems/497c346b-f5bf-4794-a231-58f26b79820c
-- title:
--   Deterministic annual cash cost shifts entropic stage value equally
-- statement:
--   Adding a deterministic immediate cost k to every next-state outcome under the selected action multiplies the conditional exponential moment by exp(gamma*k), whose logarithm shifts by gamma*k. Division by nonzero gamma yields a shift of k in the stage value. Normalised nonnegative transition weights guarantee positive log arguments.
--
--   **Mathematical statement**
--
--   $$
--   Q_{\gamma,\beta}(c+k,F)=Q_{\gamma,\beta}(c,F)+k
--   $$
-- source:
--   Bäuerle and Glauner (2022), Markov decision processes with recursive risk measures, European Journal of Operational Research 296(3), Definition 4.6, Theorem 4.7, equation (4.2), DOI https://doi.org/10.1016/j.ejor.2021.04.030; Bäuerle and Jaśkiewicz (2024), entropic certainty equivalent, Example 1(a), equation (2), DOI https://doi.org/10.1007/s00186-024-00857-0; derived finite-state discrete-time insurer cost specialisation

import Mathlib
import Definitions.Def_actuarial_finiteEntropicStageCost

namespace ActuarialValuation

theorem finiteEntropicStageCost_cash_add {S A : Type*} [Fintype S]
  (P : S → A → S → ℝ) (cost : S → A → S → ℝ)
  (beta gamma : ℝ) (next : S → ℝ) (s : S) (a : A) (k : ℝ)
  (hP : ∀ t, 0 ≤ P s a t)
  (hsum : (∑ t : S, P s a t) = 1)
  (hgamma : gamma ≠ 0) :
  finiteEntropicStageCost P (fun x b t => cost x b t + k)
      beta gamma next s a =
    finiteEntropicStageCost P cost beta gamma next s a + k := by sorry

end ActuarialValuation
