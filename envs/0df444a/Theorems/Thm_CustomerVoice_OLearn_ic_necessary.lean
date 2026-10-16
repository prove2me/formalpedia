-- Prove2me | Theorems.Thm_CustomerVoice_OLearn_ic_necessary
-- name    : CustomerVoice.OLearn.ic_necessary
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T01:07:57.784831+00:00
-- url     : https://prove2.me/theorems/4d282542-40bd-4732-b9ca-fba2d97eecd6
-- title:
--   §3.3, p. 17, (11)–(12) — if the first-best requests q*(θH), q*(θL) form a separating equilibrium, then IC′_H and IC′_L hold
-- statement:
--   Under the standing assumptions, suppose that the request profile $q^O_H=q^*(\theta_H)$, $q^O_L=q^*(\theta_L)$ together with some belief function $\hat\theta(\cdot)$ is a separating equilibrium of the O-Learning game. Then both incentive constraints hold:
--   $$\mathrm{IC}'_H:\ \mu(q^*(\theta_H),\theta_H,\theta_H)\ge\mu(q^*(\theta_L),\theta_H,\theta_L),\qquad \mathrm{IC}'_L:\ \mu(q^*(\theta_L),\theta_L,\theta_L)\ge\mu(q^*(\theta_H),\theta_L,\theta_H).$$
--
--   The statement holds for every belief function, whatever it assigns off the equilibrium path. It is the necessity half of Proposition 3.
-- source:
--   Guo, The Voice of Customers in Customization, SSRN working paper 3994319 (version of 2023-11-29, https://ssrn.com/abstract=3994319), pp. 16–17, §3.3, (11)–(12)

import Mathlib
import Definitions.Def_CustomerVoice_OLearn_Setting

namespace CustomerVoice.OLearn

theorem ic_necessary (M : Model) (hM : M.Standing) :
    ∀ bel : ℝ → CustomerVoice.ALearn.BType, M.OSepEq M.qO bel → M.ICH' ∧ M.ICL' := by sorry

end CustomerVoice.OLearn
