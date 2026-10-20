-- Prove2me | Theorems.Thm_ContestDuration_Patient_equilibrium_effort
-- name    : ContestDuration.Patient.equilibrium_effort
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:23:44.421914+00:00
-- url     : https://prove2.me/theorems/4c4f06e1-f358-450b-9ef1-e0c627896a45
-- title:
--   Equations (3)–(5) — equilibrium effort satisfies the first-order condition
-- statement:
--   Under the fixed-award contest assumptions, suppose the marginal award-weighted rank probability $x=\sum_{j=1}^N I_j^N\gamma(j)$ is positive. For positive duration $T$ and positive productivity, the effort defined by equation (5) is positive and is the unique positive solution of
--
--   $$\sum_{j=1}^N I_j^N A(j)=cb(e^*)^{b-1}\tau(T)^{1-b},\qquad A(j)=A\gamma(j).$$
--
--   This is the equilibrium first-order condition used when the organizer evaluates profit and participation.
--
--   **Formalization Note** The statement identifies the unique positive solution of the first-order condition. It does not assert global optimality of the agent's best response in equation (7); that issue is treated separately in the paper's Online Appendix.
-- source:
--   Korpeoglu, Körpeoğlu & Tunç, Optimal Duration of Innovation Contests, SSRN 3064763 (authors' version, forthcoming at M&SOM; PDF of 2020-07-23), p. 12, equations (3)–(5)

import Mathlib
import Definitions.Def_ContestDuration_Patient_Model

namespace ContestDuration.Patient

theorem equilibrium_effort (P : Params) (hS : P.Standing) (h : ℝ → ℝ)
    (hh : ShockOK h) (hx : 0 < xOf P h) (θ : ℝ → ℝ)
    (hθ : ProductivityOK θ) (T : ℝ) (hT : 0 < T) :
    0 < effort P θ h T ∧
    (∑ j ∈ Finset.Icc 1 P.N, Irank P.N j h * (P.γ j * P.A) =
      P.c * P.b * (effort P θ h T) ^ (P.b - 1) * tau P.b θ T ^ (1 - P.b)) ∧
    (∀ e : ℝ, 0 < e →
      (∑ j ∈ Finset.Icc 1 P.N, Irank P.N j h * (P.γ j * P.A) =
        P.c * P.b * e ^ (P.b - 1) * tau P.b θ T ^ (1 - P.b)) →
      e = effort P θ h T) := by sorry

end ContestDuration.Patient
