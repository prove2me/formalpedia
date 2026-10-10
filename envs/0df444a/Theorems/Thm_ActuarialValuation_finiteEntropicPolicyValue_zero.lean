-- Prove2me | Theorems.Thm_ActuarialValuation_finiteEntropicPolicyValue_zero
-- name    : ActuarialValuation.finiteEntropicPolicyValue_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T09:44:52.855983+00:00
-- url     : https://prove2.me/theorems/ef87c36f-edc3-4041-8361-6f18f1643ea4
-- title:
--   A zero-year Markov policy has its terminal cost
-- statement:
--   For a horizon of zero policy years there is no action, no transition and no covered future cashflow. The fixed policy's recursively valued insurance cost equals the supplied terminal valuation for the current state. The result holds for arbitrary risk and discount parameters because the stage operator is never invoked.
--
--   **Mathematical statement**
--
--   $$
--   J^\pi_0(s)=h(s)
--   $$
-- source:
--   Bäuerle and Glauner (2022), Markov decision processes with recursive risk measures, European Journal of Operational Research 296(3), Definition 4.6, Theorem 4.7, equation (4.2), DOI https://doi.org/10.1016/j.ejor.2021.04.030; Bäuerle and Jaśkiewicz (2024), entropic certainty equivalent, Example 1(a), equation (2), DOI https://doi.org/10.1007/s00186-024-00857-0; derived finite-state discrete-time insurer cost specialisation

import Mathlib
import Definitions.Def_actuarial_finiteEntropicPolicyValue

namespace ActuarialValuation

theorem finiteEntropicPolicyValue_zero {S A : Type*}
  [Fintype S] (P : S → A → S → ℝ)
  (cost : S → A → S → ℝ) (beta gamma : ℝ)
  (terminal : S → ℝ) (policy : ℕ → S → A) (s : S) :
  finiteEntropicPolicyValue P cost beta gamma terminal policy 0 s =
    terminal s := by sorry

end ActuarialValuation
