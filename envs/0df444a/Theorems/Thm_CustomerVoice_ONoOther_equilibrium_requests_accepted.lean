-- Prove2me | Theorems.Thm_CustomerVoice_ONoOther_equilibrium_requests_accepted
-- name    : CustomerVoice.ONoOther.equilibrium_requests_accepted
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T01:07:46.390776+00:00
-- url     : https://prove2.me/theorems/449079fe-6665-452a-8636-a52b207fbda8
-- title:
--   Appendix, p. 29 — case 2 equilibrium requests satisfy seller acceptance bounds
-- statement:
--   Let the O-Learning model satisfy its standing assumptions and $\theta_H/\theta_L<\Lambda_L$. For any separating pure-strategy equilibrium with requests $q_H,q_L$ and any on-path-consistent belief function, both requests lie within the corresponding seller acceptance ranges:
--   $$
--   q_H\le\frac{\gamma\theta_H}{s+\gamma k},\qquad q_L\le\frac{\gamma\theta_L}{s+\gamma k}.
--   $$
--   These are the feasibility bounds the Appendix uses before comparing the two types' incentives to imitate.
--
--   **Formalization Note** Acceptance uses the paper's payoff inequality, including acceptance at equality. A rejected request pays zero, so equilibrium optimality has content at this step.
-- source:
--   Guo, The Voice of Customers in Customization, SSRN working paper 3994319 (version of 2023-11-29, https://ssrn.com/abstract=3994319), p. 29, Appendix, No Other Separating Equilibrium under the O-Learning Customization

import Mathlib
import Definitions.Def_CustomerVoice_ONoOther_Setting

namespace CustomerVoice.ONoOther

theorem equilibrium_requests_accepted (M : Model) (hM : M.Standing)
    (hr : M.θH / M.θL < M.LambdaL)
    (req : CustomerVoice.ALearn.BType → ℝ) (bel : ℝ → CustomerVoice.ALearn.BType) (heq : M.OSepEq req bel) :
    req .H ≤ M.γ * M.θH / (M.s + M.γ * M.k) ∧
      req .L ≤ M.γ * M.θL / (M.s + M.γ * M.k) := by sorry

end CustomerVoice.ONoOther
