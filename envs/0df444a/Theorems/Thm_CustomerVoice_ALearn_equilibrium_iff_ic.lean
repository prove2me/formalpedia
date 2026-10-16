-- Prove2me | Theorems.Thm_CustomerVoice_ALearn_equilibrium_iff_ic
-- name    : CustomerVoice.ALearn.equilibrium_iff_ic
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T23:13:02.570613+00:00
-- url     : https://prove2.me/theorems/2535d640-67bf-4e3d-a310-09397410c56c
-- title:
--   §3.2, p. 12, (6)–(7) — informative equilibrium iff both incentive conditions hold
-- statement:
--   In the two-type A-Learning game under its standing assumptions, an informative separating equilibrium exists if and only if both buyer types prefer truthful communication to imitating the other type:
--   $$u(\theta_H,\theta_H)\geq u(\theta_H,\theta_L)\quad\text{and}\quad u(\theta_L,\theta_L)\geq u(\theta_L,\theta_H).$$
--   Here $u(\theta,\hat\theta)$ is the buyer's expected payoff when its actual type is $\theta$, the seller believes $\hat\theta$, and the seller designs at its optimum for that belief.
--
--   The equivalence connects the full cheap-talk equilibrium conditions to the two explicit incentive constraints (6) and (7).
--
--   **Formalization Note** An equilibrium includes a separating message rule, on-path belief consistency, attained seller optimality over nonnegative quality, and buyer optimality against every message. The pricing stage is represented by equation (5).
-- source:
--   Guo, The Voice of Customers in Customization, SSRN working paper 3994319 (version of 2023-11-29, https://ssrn.com/abstract=3994319), p. 12, §3.2, (5)–(7)

import Mathlib
import Definitions.Def_CustomerVoice_ALearn_Setting

namespace CustomerVoice.ALearn

/-- §3.2, p. 12, equations (6)–(7): truthful informative communication is
an equilibrium exactly when both incentive conditions hold. -/
theorem equilibrium_iff_ic (M : Model) (hM : M.Standing) :
    M.InformativeEq ↔ M.ICH ∧ M.ICL := by sorry

end CustomerVoice.ALearn
