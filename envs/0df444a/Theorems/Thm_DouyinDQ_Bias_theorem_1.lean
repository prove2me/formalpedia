-- Prove2me | Theorems.Thm_DouyinDQ_Bias_theorem_1
-- name    : DouyinDQ.Bias.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:05:36.809767+00:00
-- url     : https://prove2.me/theorems/134cfc6f-97be-4ebf-be1f-0ca4a98d7ab5
-- title:
--   Theorem 1, p. 6 — DQ bias at most T_abs³ r_max δ²
-- statement:
--   In the finite absorbing MDP of Section 3, let $\pi_0$ always choose control, $\pi_1$ always choose treatment, and $\pi_{1/2}$ choose each with probability $1/2$ at every step. The common zero-reward absorbing class has expected absorption time strictly below $T_{\rm abs}$ from every state under all three policies. Suppose the transition rows for the two actions satisfy $D_{\rm TV}(P_1(s,\cdot),P_0(s,\cdot))\le\delta$ for every state, and let $r_{\max}=\max_{s,a}|r(s,a)|$. Then the expectations of the trajectory estimator (4), truncated at time $H$, converge to a number $L$ and
--   $$
--   |{\rm ATE}-L|\le T_{\rm abs}^{3}r_{\max}\delta^2,
--   \qquad {\rm ATE}=J_{\pi_1}-J_{\pi_0}.
--   $$
--   This is the paper's second-order bound on the bias of the Differences-in-Qs estimator.
--
--   **Formalization Note** $L$ is the limit of actual finite-trajectory estimator expectations, not an expansion defined in terms of $Q$ functions. Rewards are conditional means. The absorbing class is read as closed with zero reward. The paper leaves $D_{\rm TV}$ undefined; the bound uses the total-variation norm $\sum_{s'}|P_1(s,s')-P_0(s,s')|$. With the half-$\ell_1$ convention, the printed constant fails, with ratios approaching $2$.
-- source:
--   Farias, Li, Peng, Ren, Zhang, Zheng, Correcting for Interference in Experiments: A Case Study at Douyin, arXiv:2305.02542v1, p. 6, Theorem 1; pp. 3–5, §3 and Eq. (4)

import Definitions.Def_DouyinDQ_Bias_Model

namespace DouyinDQ.Bias

/-- Theorem 1, p. 6: second-order bias of the trajectory Differences-in-Qs estimator. -/
theorem theorem_1 {S : Type} [Fintype S] [DecidableEq S]
    (M : MDP S (Fin 2)) (hM : M.Standing)
    (Sabs : Set S) [DecidablePred (· ∈ Sabs)] (Tabs δ : ℝ)
    (hA1 : Assumption1 M Sabs Tabs)
    (hδ : ∀ s, ∑ s', |M.P 1 s s' - M.P 0 s s'| ≤ δ) :
    ∃ L : ℝ,
      Filter.Tendsto (fun H => expDQTrunc M H) Filter.atTop (nhds L) ∧
      |ATE M - L| ≤ Tabs ^ 3 * rmax M * δ ^ 2 := by sorry

end DouyinDQ.Bias
