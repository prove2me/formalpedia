-- Prove2me | Theorems.Thm_CustomerVoice_ALearn_ich_iff_threshold
-- name    : CustomerVoice.ALearn.ich_iff_threshold
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T23:13:42.101008+00:00
-- url     : https://prove2.me/theorems/f2a9d59f-633d-4338-983d-bc61d6ea5ca4
-- title:
--   §3.2, p. 13 — high-type incentive condition iff θH/θL ≥ ΔH
-- statement:
--   Under the A-Learning model's standing assumptions, the high-type buyer weakly prefers truthful communication to imitating the low type if and only if
--   $$\frac{\theta_H}{\theta_L}\geq\Delta_H=\frac{\gamma[2s+(1+\gamma)k]}{(1-\gamma)(2s+\gamma k)}.$$
--   The buyer payoffs use the seller's design for the reported type and keep the nonpurchase option in both price-setting cases.
--
--   This gives the high-type component of the threshold in Proposition 1.
--
--   **Formalization Note** The weak inequality is the statement on p. 13 and in Proposition 1. The Appendix's corresponding strict-inequality line is read at equality using the weak incentive condition (6).
-- source:
--   Guo, The Voice of Customers in Customization, SSRN working paper 3994319 (version of 2023-11-29, https://ssrn.com/abstract=3994319), p. 13, §3.2, high-type threshold sentence following Proposition 1

import Mathlib
import Definitions.Def_CustomerVoice_ALearn_Setting

namespace CustomerVoice.ALearn

/-- §3.2, p. 13: the high-type IC condition is the threshold condition. -/
theorem ich_iff_threshold (M : Model) (hM : M.Standing) :
    M.ICH ↔ M.θH / M.θL ≥ M.DeltaH := by sorry

end CustomerVoice.ALearn
