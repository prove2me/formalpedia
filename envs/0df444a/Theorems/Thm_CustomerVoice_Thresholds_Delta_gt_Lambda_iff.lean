-- Prove2me | Theorems.Thm_CustomerVoice_Thresholds_Delta_gt_Lambda_iff
-- name    : CustomerVoice.Thresholds.Delta_gt_Lambda_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T21:24:57.927414+00:00
-- url     : https://prove2.me/theorems/2c1b8edb-93b2-41cb-9989-2a1f31ae2309
-- title:
--   Proof of Proposition 7, p. 29 — Δ > Λ iff Δ_L > min{Λ_{H1}, Λ_{H2}}
-- statement:
--   Let $(\theta_H,\theta_L,\alpha,\gamma,k,s)$ satisfy the standing assumptions $\theta_H>\theta_L>0$, $\alpha,\gamma\in(0,1)$, $k>0$, $s>0$, and let $\Delta=\max\{\Delta_H,\Delta_L\}$ and $\Lambda=\max\{\min\{\Lambda_{H1},\Lambda_{H2}\},\Lambda_L\}$ be the A-Learning and O-Learning critical values. Then
--   $$\Delta>\Lambda\quad\Longleftrightarrow\quad\Delta_L>\min\{\Lambda_{H1},\Lambda_{H2}\}.$$
--
--   This reduces the comparison of the two critical values, each a maximum of several expressions, to a single comparison between the low type's A-Learning threshold and the smaller high-type O-Learning threshold.
-- source:
--   Guo, The Voice of Customers in Customization, SSRN working paper 3994319 (version of 2023-11-29, https://ssrn.com/abstract=3994319), p. 29, Appendix, Proof of Proposition 7

import Mathlib
import Definitions.Def_CustomerVoice_Thresholds_Setting

namespace CustomerVoice.Thresholds

theorem Delta_gt_Lambda_iff (M : Model) (hM : M.Standing) :
    M.Delta > M.Lambda ↔ M.DeltaL > min M.LambdaH1 M.LambdaH2 := by sorry

end CustomerVoice.Thresholds
