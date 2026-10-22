-- Prove2me | Theorems.Thm_FollowCrowd_Inference_congestion_effect
-- name    : FollowCrowd.Inference.congestion_effect
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:17:10.487988+00:00
-- url     : https://prove2.me/theorems/407d5002-e7e5-40cd-8c18-13556592a3ab
-- title:
--   §4.1, p. 9 — congestion effect: more joining by others makes the queue stochastically longer for each known capacity
-- statement:
--   Under the standing assumptions, fix the capacity $\mu = \mu_X$, $X\in\{H,L\}$, and let $p^-$ and $p'^-$ be joining vectors ($p^-_0 = p'^-_0 = 1$, coordinates in $[0,1]$) with $p^-_i \le p'^-_i$ for every $i$. Then for every $m$,
--   $$\sum_{n=0}^{m}\pi_X(n,p'^-) \le \sum_{n=0}^{m}\pi_X(n,p^-).$$
--
--   In words: when the other customers' tendency to join increases, the queue length an arriving customer observes is larger in the usual stochastic order. In particular, when the capacity is known, so that a customer joins exactly at queue lengths up to a fixed threshold, the ex-ante joining probability $\sum_{n\le m}\pi_X(n,\cdot)$ decreases: this is the congestion effect, the force behind avoid-the-crowd behaviour.
--
--   **Formalization Note** The paper states the congestion effect in words; it is formalized as first-order stochastic dominance of the queue-length law, which contains the paper's claim about the ex-ante joining probability under known capacity.
-- source:
--   Yang, Shang & Liu, Follow the crowd with uncertain service capacity, SSRN 4159035 (version of June 24, 2022), p. 9, §4.1, congestion effect paragraph

import Mathlib
import Definitions.Def_FollowCrowd_Inference_Model

namespace FollowCrowd.Inference

theorem congestion_effect (P : Params) (hP : P.Standing) (mu : ℝ)
    (hmu : mu = P.muH ∨ mu = P.muL) (p p' : ℕ → ℝ) (hp : IsJoinVec p) (hp' : IsJoinVec p')
    (hle : ∀ i, p i ≤ p' i) (m : ℕ) :
    ∑ n ∈ Finset.range (m + 1), stat P mu p' n ≤
      ∑ n ∈ Finset.range (m + 1), stat P mu p n := by sorry

end FollowCrowd.Inference
