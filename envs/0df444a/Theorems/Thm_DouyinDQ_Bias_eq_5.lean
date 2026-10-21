-- Prove2me | Theorems.Thm_DouyinDQ_Bias_eq_5
-- name    : DouyinDQ.Bias.eq_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:05:38.880063+00:00
-- url     : https://prove2.me/theorems/29b7a4c1-b078-4f61-bc6c-04977271f3f2
-- title:
--   Equation (5), p. 5 — expectation of the DQ estimator
-- statement:
--   Run the experiment with treatment probability $1/2$ at each step in an absorbing finite MDP. Let $\widehat{\rm ATE}^{(H)}_{\rm DQ}$ be equation (4) truncated at time $H$. Its expectations converge to a real number $L$, and the series of expected differences of state-action $Q$ functions sums to that same number:
--   $$
--   L=\lim_{H\to\infty}\mathbb E_{\pi_{1/2}}[\widehat{\rm ATE}^{(H)}_{\rm DQ}]
--   =\sum_{t=0}^{\infty}\mathbb E_{\pi_{1/2}}[Q_{\pi_{1/2}}(s_t,1)-Q_{\pi_{1/2}}(s_t,0)].
--   $$
--   This identifies the trajectory-level estimator with the value expression used in the paper.
--
--   **Formalization Note** The infinite estimator expectation is the limit of finite path expectations. Its existence and the convergence of the displayed series are conclusions.
-- source:
--   Farias, Li, Peng, Ren, Zhang, Zheng, Correcting for Interference in Experiments: A Case Study at Douyin, arXiv:2305.02542v1, p. 5, Eq. (5) and Eq. (4)

import Definitions.Def_DouyinDQ_Bias_Model

namespace DouyinDQ.Bias

/-- Equation (5), p. 5: expected trajectory DQ equals the occupancy sum of Q differences. -/
theorem eq_5 {S : Type} [Fintype S] [DecidableEq S]
    (M : MDP S (Fin 2)) (hM : M.Standing)
    (Sabs : Set S) [DecidablePred (· ∈ Sabs)] (T : ℝ)
    (habs : IsAbsorbingFor M Sabs piHalf)
    (ht : AbsTimeLT M Sabs piHalf T) :
    ∃ L : ℝ,
      Filter.Tendsto (fun H => expDQTrunc M H) Filter.atTop (nhds L) ∧
      HasSum (fun t : ℕ => pathExp M piHalf t
        (fun ω => Qsa M piHalf (ω (Fin.last t)).1 1 -
          Qsa M piHalf (ω (Fin.last t)).1 0)) L := by sorry

end DouyinDQ.Bias
