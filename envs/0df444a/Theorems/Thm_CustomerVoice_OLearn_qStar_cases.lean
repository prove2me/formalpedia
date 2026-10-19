-- Prove2me | Theorems.Thm_CustomerVoice_OLearn_qStar_cases
-- name    : CustomerVoice.OLearn.qStar_cases
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T01:07:50.645065+00:00
-- url     : https://prove2.me/theorems/a7d2e878-f5d8-43dc-a877-a2c5f3288392
-- title:
--   Appendix, Proof of Proposition 3, p. 28 — q*(θ) = γθ/(s+γk) when γ ≤ s/k and q*(θ) = θ/(2k) when γ ≥ s/k
-- statement:
--   Under the standing assumptions, for each buyer type with preference $\theta\in\{\theta_H,\theta_L\}$,
--   $$q^*(\theta)=\begin{cases}\dfrac{\gamma\theta}{s+\gamma k}, & \gamma\le s/k,\\[2mm] \dfrac{\theta}{2k}, & \gamma\ge s/k.\end{cases}$$
--
--   The two regimes are the ones in which the seller's acceptance constraint binds or does not bind at the first-best design, and the proof of Proposition 3 treats them separately.
-- source:
--   Guo, The Voice of Customers in Customization, SSRN working paper 3994319 (version of 2023-11-29, https://ssrn.com/abstract=3994319), p. 28, Appendix, Proof of Proposition 3

import Mathlib
import Definitions.Def_CustomerVoice_OLearn_Setting

namespace CustomerVoice.OLearn

theorem qStar_cases (M : Model) (hM : M.Standing) (t : CustomerVoice.ALearn.BType) :
    (M.γ ≤ M.s / M.k → M.qStar (M.θ t) = M.γ * M.θ t / (M.s + M.γ * M.k)) ∧
    (M.s / M.k ≤ M.γ → M.qStar (M.θ t) = M.θ t / (2 * M.k)) := by sorry

end CustomerVoice.OLearn
