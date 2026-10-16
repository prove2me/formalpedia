-- Prove2me | Theorems.Thm_CustomerVoice_ONoOther_low_case_gamma
-- name    : CustomerVoice.ONoOther.low_case_gamma
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T01:07:50.43592+00:00
-- url     : https://prove2.me/theorems/96a05fb2-0a60-4180-b5bd-14a09b7bdbd3
-- title:
--   Appendix, p. 29 — low-case failure implies γ < s/k and q*(θ) is acceptance-bound
-- statement:
--   Let the O-Learning model satisfy its standing assumptions. If $\theta_H/\theta_L<\Lambda_L=s/(\gamma k)$, then $\gamma<s/k$. For either buyer type $t\in\{H,L\}$, with preference $\theta_t$, this gives
--   $$
--   q^*(\theta_t)=\frac{\gamma\theta_t}{s+\gamma k}<\frac{\theta_t}{2k}.
--   $$
--   The complete-information request is therefore at the seller's acceptance boundary in the Appendix's second case.
--
--   **Formalization Note** The paper also calls $\theta_t/(2k)$ the unconstrained maximizer of $\mu(q,\theta_t,\theta_t)$; that separate optimality claim is not included here.
-- source:
--   Guo, The Voice of Customers in Customization, SSRN working paper 3994319 (version of 2023-11-29, https://ssrn.com/abstract=3994319), p. 29, Appendix, No Other Separating Equilibrium under the O-Learning Customization

import Mathlib
import Definitions.Def_CustomerVoice_ONoOther_Setting

namespace CustomerVoice.ONoOther

theorem low_case_gamma (M : Model) (hM : M.Standing)
    (hr : M.θH / M.θL < M.LambdaL) :
    M.γ < M.s / M.k ∧
      ∀ t : CustomerVoice.ALearn.BType,
        M.qStar (M.θ t) = M.γ * M.θ t / (M.s + M.γ * M.k) ∧
        M.γ * M.θ t / (M.s + M.γ * M.k) < M.θ t / (2 * M.k) := by sorry

end CustomerVoice.ONoOther
