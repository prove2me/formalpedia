-- Prove2me | Theorems.Thm_FollowCrowd_Inference_lemma_2
-- name    : FollowCrowd.Inference.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:17:12.811511+00:00
-- url     : https://prove2.me/theorems/a9c4f3dc-5da0-43da-a875-1148f6319a55
-- title:
--   Lemma 2, p. 9 — inference effect: raising the others' joining probability at a reachable state below N̄ raises θn(p⁻) at every n
-- statement:
--   Under the standing assumptions, let $p^-$ and $p^- + \Delta$ be joining vectors ($p^-_0 = 1$, all coordinates in $[0,1]$) with $\Delta_i \ge 0$ for every $i$. Suppose there is a state $n' < \bar N$ that is recurrent under $p^-$, i.e. $\prod_{i=0}^{n'-1}p^-_i > 0$, with $\Delta_{n'} > 0$. Then for every queue length $n$,
--   $$\theta_n(p^- + \Delta) > \theta_n(p^-).$$
--
--   When the other customers are more willing to join, a given queue length is more likely to have been produced by fast service, so the belief of high capacity rises: this is the inference effect, which competes with the congestion effect and can make the best response follow the crowd.
--
--   **Formalization Note** The paper's condition "$\Delta_{n'} > 0$ for at least one recurrent state $n'$" is read as $\prod_{i<n'}p^-_i > 0$. The guard $n' < \bar N$ is added: the coordinate $p^-_{\bar N}$ never enters the law (2)–(3), so a change only there leaves every $\theta_n$ unchanged. The paper states the inequality as a condition a rational inference "must satisfy"; it is formalized as the implication it asserts.
-- source:
--   Yang, Shang & Liu, Follow the crowd with uncertain service capacity, SSRN 4159035 (version of June 24, 2022), p. 9, Lemma 2 (with the Δ conditions of the ATC/FTC definition, p. 9); proof: Online Appendix p. 1 (PDF 25)

import Mathlib
import Definitions.Def_FollowCrowd_Inference_Model

namespace FollowCrowd.Inference

theorem lemma_2 (P : Params) (hP : P.Standing) (p p' : ℕ → ℝ) (hp : IsJoinVec p)
    (hp' : IsJoinVec p') (hle : ∀ i, p i ≤ p' i)
    (hstrict : ∃ n' < Nbar P, 0 < ∏ i ∈ Finset.range n', p i ∧ p n' < p' n') :
    ∀ n, theta P p n < theta P p' n := by sorry

end FollowCrowd.Inference
