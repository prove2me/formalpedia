-- Prove2me | Theorems.Thm_FollowCrowd_Inference_stat_continuous_v
-- name    : FollowCrowd.Inference.stat_continuous_v
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:17:10.481001+00:00
-- url     : https://prove2.me/theorems/532a5dfc-1f25-4f50-8799-4cda9f8e5f4f
-- title:
--   Proof of Proposition 2, Online Appendix p. 1 — ΠX(n, v) is continuous in v
-- statement:
--   Under the standing assumptions, for $X \in \{H, L\}$ and every queue length $n$, the stationary probability $\pi_X(n, p^-(v))$ of state $n$ under the threshold profile $p^-(v)$ is a continuous function of $v$ on $[0,\infty)$:
--   $$v \mapsto \pi_X(n, p^-(v)) \in C([0,\infty)).$$
--
--   The threshold profile interpolates linearly between consecutive integer thresholds, so the law of the queue moves continuously with $v$; the proof of Proposition 2 uses this to compare $JP^U(v+\delta)$ with $JP^U(v)$ for small $\delta$.
-- source:
--   Yang, Shang & Liu, Follow the crowd with uncertain service capacity, SSRN 4159035 (version of June 24, 2022), Online Appendix p. 1 (PDF 25), proof of Proposition 2, last sentence (first clause)

import Mathlib
import Definitions.Def_FollowCrowd_Inference_Model

namespace FollowCrowd.Inference

theorem stat_continuous_v (P : Params) (hP : P.Standing) (mu : ℝ)
    (hmu : mu = P.muH ∨ mu = P.muL) (n : ℕ) :
    ContinuousOn (fun v => stat P mu (thrProfile v) n) (Set.Ici 0) := by sorry

end FollowCrowd.Inference
