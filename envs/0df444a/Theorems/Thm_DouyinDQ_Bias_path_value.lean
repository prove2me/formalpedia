-- Prove2me | Theorems.Thm_DouyinDQ_Bias_path_value
-- name    : DouyinDQ.Bias.path_value
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:05:49.94125+00:00
-- url     : https://prove2.me/theorems/1c11341e-c768-4ba6-a69d-6ff69d0f72c9
-- title:
--   §5.3, p. 8 — trajectory reward equals the value functional
-- statement:
--   For a stationary policy $\pi$ of the finite MDP, assume a closed zero-reward absorbing class and a finite expected time outside it from every state. The series of expected rewards calculated directly from the finite state-action path law sums to the total-reward value functional:
--   $$
--   \sum_{t=0}^{\infty}\mathbb E_\pi[r_t]=\widetilde E_\pi r_\pi.
--   $$
--   The assertion includes convergence of the path-reward series. It connects the target estimand $J_\pi$ to the value-functional expansion used in Section 5.3.
--
--   **Formalization Note** The convergence is expressed by `HasSum`; a divergent real `tsum` would otherwise default to zero in Lean.
-- source:
--   Farias, Li, Peng, Ren, Zhang, Zheng, Correcting for Interference in Experiments: A Case Study at Douyin, arXiv:2305.02542v1, p. 8, §5.3, first paragraph

import Definitions.Def_DouyinDQ_Bias_Model

namespace DouyinDQ.Bias

/-- Section 5.3, p. 8: the trajectory total reward is the value functional. -/
theorem path_value {S A : Type} [Fintype S] [DecidableEq S]
    [Fintype A] [DecidableEq A]
    (M : MDP S A) (hM : M.Standing)
    (Sabs : Set S) [DecidablePred (· ∈ Sabs)] (T : ℝ)
    (π : S → A → ℝ) (hπ : IsPolicy π)
    (habs : IsAbsorbingFor M Sabs π) (ht : AbsTimeLT M Sabs π T) :
    HasSum (fun t : ℕ => pathExp M π t
      (fun ω => M.r (ω (Fin.last t)).1 (ω (Fin.last t)).2))
      (Etilde M π (rpol M π)) := by sorry

end DouyinDQ.Bias
