-- Prove2me | Theorems.Thm_CustomerVoice_ALearn_icl_iff_threshold
-- name    : CustomerVoice.ALearn.icl_iff_threshold
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T23:13:04.873588+00:00
-- url     : https://prove2.me/theorems/5c366b26-b1fd-40be-8773-897ddebf1f18
-- title:
--   §3.2, p. 13 — low-type incentive condition iff θH/θL ≥ ΔL
-- statement:
--   Under the A-Learning model's standing assumptions, the low-type buyer weakly prefers truthful communication to overstating its preference if and only if
--   $$\frac{\theta_H}{\theta_L}\geq\Delta_L=\frac{2s+\gamma k}{\gamma k}.$$
--   The buyer payoff allows the low type to decline a product priced above its valuation.
--
--   This gives the low-type component of the threshold in Proposition 1.
--
--   **Formalization Note** The weak inequality is the statement on p. 13 and in Proposition 1. The `max` with zero in the payoff is essential for the low type's deviation; the pricing stage enters through equation (5).
-- source:
--   Guo, The Voice of Customers in Customization, SSRN working paper 3994319 (version of 2023-11-29, https://ssrn.com/abstract=3994319), p. 13, §3.2, low-type threshold sentence following Proposition 1

import Mathlib
import Definitions.Def_CustomerVoice_ALearn_Setting

namespace CustomerVoice.ALearn

/-- §3.2, p. 13: the low-type IC condition is the threshold condition. -/
theorem icl_iff_threshold (M : Model) (hM : M.Standing) :
    M.ICL ↔ M.θH / M.θL ≥ M.DeltaL := by sorry

end CustomerVoice.ALearn
