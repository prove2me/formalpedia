-- Prove2me | Theorems.Thm_CustomerVoice_Thresholds_DeltaH_lt_LambdaH1
-- name    : CustomerVoice.Thresholds.DeltaH_lt_LambdaH1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T21:24:46.637849+00:00
-- url     : https://prove2.me/theorems/dd526cb5-a0e2-4e33-8bdc-24d88588b208
-- title:
--   Proof of Proposition 7, p. 29 — Δ_H < Λ_{H1}
-- statement:
--   Let $(\theta_H,\theta_L,\alpha,\gamma,k,s)$ satisfy the standing assumptions $\theta_H>\theta_L>0$, $\alpha,\gamma\in(0,1)$, $k>0$, $s>0$. Then the high type's A-Learning threshold is strictly smaller than the first high-type O-Learning threshold:
--   $$\Delta_H=\frac{\gamma[2s+(1+\gamma)k]}{(1-\gamma)(2s+\gamma k)}<\Lambda_{H1}=\frac{\gamma(s+k)}{(1-\gamma)s}.$$
--
--   This is the first of the three comparisons in the proof of Proposition 7: the high type's incentive to tell the truth binds at a lower ratio $\theta_H/\theta_L$ under A-Learning than under O-Learning when the seller-acceptance constraint binds.
-- source:
--   Guo, The Voice of Customers in Customization, SSRN working paper 3994319 (version of 2023-11-29, https://ssrn.com/abstract=3994319), p. 29, Appendix, Proof of Proposition 7

import Mathlib
import Definitions.Def_CustomerVoice_Thresholds_Setting

namespace CustomerVoice.Thresholds

theorem DeltaH_lt_LambdaH1 (M : Model) (hM : M.Standing) :
    M.DeltaH < M.LambdaH1 := by sorry

end CustomerVoice.Thresholds
