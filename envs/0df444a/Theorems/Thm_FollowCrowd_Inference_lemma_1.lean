-- Prove2me | Theorems.Thm_FollowCrowd_Inference_lemma_1
-- name    : FollowCrowd.Inference.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T05:17:13.559801+00:00
-- url     : https://prove2.me/theorems/da3e4a1b-a2d1-4a30-bd5f-b6d93b9286a4
-- title:
--   Lemma 1, p. 8 — for any p⁻, θn(p⁻) and u(n, p⁻) (strictly) decrease in n
-- statement:
--   Under the standing assumptions, let $p^- = (1, p^-_1,\dots)$ be any joining vector with $p^-_i\in[0,1]$. Then
--
--   1. the belief $\theta_n(p^-)$ of high capacity is strictly decreasing in the observed queue length $n$, and
--   2. the expected utility of joining $u(n,p^-) = R - C(n+1)\bigl[\theta_n(p^-)/\mu_H + (1-\theta_n(p^-))/\mu_L\bigr]$ is strictly decreasing in $n$:
--   $$m < n \implies \theta_n(p^-) < \theta_m(p^-) \text{ and } u(n,p^-) < u(m,p^-).$$
--
--   A longer queue is evidence of slow service and is costlier to wait in; both effects lower the value of joining. This monotonicity is what makes the best response a threshold strategy (Proposition 1).
--
--   **Formalization Note** The page says "decreases"; the proof (Online Appendix p. 1) shows strict decrease, which is stated here for all $n \in \mathbb N$ (the belief (A-1) is defined at every $n$).
-- source:
--   Yang, Shang & Liu, Follow the crowd with uncertain service capacity, SSRN 4159035 (version of June 24, 2022), p. 8, Lemma 1; proof: Online Appendix p. 1 (PDF 25)

import Mathlib
import Definitions.Def_FollowCrowd_Inference_Model

namespace FollowCrowd.Inference

theorem lemma_1 (P : Params) (hP : P.Standing) (p : ℕ → ℝ) (hp : IsJoinVec p) :
    StrictAnti (theta P p) ∧ StrictAnti (util P p) := by sorry

end FollowCrowd.Inference
