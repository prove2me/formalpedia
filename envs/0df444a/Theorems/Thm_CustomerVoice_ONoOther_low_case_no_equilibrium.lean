-- Prove2me | Theorems.Thm_CustomerVoice_ONoOther_low_case_no_equilibrium
-- name    : CustomerVoice.ONoOther.low_case_no_equilibrium
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T01:07:55.650166+00:00
-- url     : https://prove2.me/theorems/4a064e5d-1572-4a01-ab66-b881aaebe314
-- title:
--   Appendix, p. 29 — case 2 has no separating equilibrium
-- statement:
--   In the two-type O-Learning customization model with its standing assumptions, suppose
--   $$
--   \frac{\theta_H}{\theta_L}<\Lambda_L=\frac{s}{\gamma k}.
--   $$
--   Then no pair of distinct nonnegative requests, under any on-path-consistent belief function, forms a separating pure-strategy equilibrium. This is the Appendix's second failure case, covering both possible orders of the two requests.
--
--   **Formalization Note** The conditional buyer payoff retains both $\max\{\cdot,0\}$ terms of equation (9); the equilibrium compares the actual payoff after seller acceptance or rejection.
-- source:
--   Guo, The Voice of Customers in Customization, SSRN working paper 3994319 (version of 2023-11-29, https://ssrn.com/abstract=3994319), p. 29, Appendix, No Other Separating Equilibrium under the O-Learning Customization

import Mathlib
import Definitions.Def_CustomerVoice_ONoOther_Setting

namespace CustomerVoice.ONoOther

theorem low_case_no_equilibrium (M : Model) (hM : M.Standing)
    (hr : M.θH / M.θL < M.LambdaL) :
    ¬ ∃ (req : CustomerVoice.ALearn.BType → ℝ) (bel : ℝ → CustomerVoice.ALearn.BType), M.OSepEq req bel := by sorry

end CustomerVoice.ONoOther
