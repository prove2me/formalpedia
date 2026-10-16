-- Prove2me | Theorems.Thm_CustomerVoice_Thresholds_DeltaL_gt_LambdaL
-- name    : CustomerVoice.Thresholds.DeltaL_gt_LambdaL
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T21:24:54.908712+00:00
-- url     : https://prove2.me/theorems/45abc40a-bf2e-4714-a3a9-4800fb24b03c
-- title:
--   Proof of Proposition 7, p. 29 — Δ_L > Λ_L
-- statement:
--   Let $(\theta_H,\theta_L,\alpha,\gamma,k,s)$ satisfy the standing assumptions $\theta_H>\theta_L>0$, $\alpha,\gamma\in(0,1)$, $k>0$, $s>0$. Then the low type's A-Learning threshold strictly exceeds its O-Learning threshold:
--   $$\Delta_L=\frac{2s+\gamma k}{\gamma k}>\Lambda_L=\frac{s}{\gamma k}.$$
--
--   This is the paper's statement that the low-type buyers' motivation for truthful revelation is lower under A-Learning than under O-Learning.
-- source:
--   Guo, The Voice of Customers in Customization, SSRN working paper 3994319 (version of 2023-11-29, https://ssrn.com/abstract=3994319), p. 29, Appendix, Proof of Proposition 7

import Mathlib
import Definitions.Def_CustomerVoice_Thresholds_Setting

namespace CustomerVoice.Thresholds

theorem DeltaL_gt_LambdaL (M : Model) (hM : M.Standing) :
    M.DeltaL > M.LambdaL := by sorry

end CustomerVoice.Thresholds
