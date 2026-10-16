-- Prove2me | Theorems.Thm_CustomerVoice_Thresholds_DeltaH_lt_LambdaH2
-- name    : CustomerVoice.Thresholds.DeltaH_lt_LambdaH2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T21:24:55.975339+00:00
-- url     : https://prove2.me/theorems/7b5f1340-ba02-4ce8-8e20-d8a58c377e8f
-- title:
--   Proof of Proposition 7, p. 29 — Δ_H < Λ_{H2}
-- statement:
--   Let $(\theta_H,\theta_L,\alpha,\gamma,k,s)$ satisfy the standing assumptions $\theta_H>\theta_L>0$, $\alpha,\gamma\in(0,1)$, $k>0$, $s>0$. Then the high type's A-Learning threshold is strictly smaller than the second high-type O-Learning threshold:
--   $$\Delta_H=\frac{\gamma[2s+(1+\gamma)k]}{(1-\gamma)(2s+\gamma k)}<\Lambda_{H2}=\frac{1+\gamma}{1-\gamma}.$$
--
--   Together with $\Delta_H<\Lambda_{H1}$ this gives $\Delta_H<\min\{\Lambda_{H1},\Lambda_{H2}\}$, the paper's statement that the high-type buyers' motivation for truthful revelation is higher under A-Learning than under O-Learning.
-- source:
--   Guo, The Voice of Customers in Customization, SSRN working paper 3994319 (version of 2023-11-29, https://ssrn.com/abstract=3994319), p. 29, Appendix, Proof of Proposition 7

import Mathlib
import Definitions.Def_CustomerVoice_Thresholds_Setting

namespace CustomerVoice.Thresholds

theorem DeltaH_lt_LambdaH2 (M : Model) (hM : M.Standing) :
    M.DeltaH < M.LambdaH2 := by sorry

end CustomerVoice.Thresholds
