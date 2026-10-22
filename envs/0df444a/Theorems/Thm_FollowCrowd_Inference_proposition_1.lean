-- Prove2me | Theorems.Thm_FollowCrowd_Inference_proposition_1
-- name    : FollowCrowd.Inference.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:17:03.897516+00:00
-- url     : https://prove2.me/theorems/d5b5a41d-fd92-445d-a357-6c8d22741df5
-- title:
--   Proposition 1, p. 8 — the best response to any p⁻ is a threshold strategy: join at 0, …, m, balk at m+1, …, N̄, with m < N̄
-- statement:
--   Under the standing assumptions, let $p^-$ be any joining vector ($p^-_0 = 1$, $p^-_i\in[0,1]$), and let $\tilde p(p^-)$ be the tagged customer's best response: join at the empty queue and whenever $u(n,p^-)\ge 0$, balk otherwise. Then there is an integer $m$ with $0 \le m < \bar N$ such that
--   $$\tilde p(p^-) = (\underbrace{1,\dots,1}_{n = 0,\dots,m}, 0, \dots, 0) \quad\text{on } \{0,\dots,\bar N\},$$
--   i.e. $\tilde p_n(p^-) = 1$ for $n \le m$ and $\tilde p_n(p^-) = 0$ for $m < n \le \bar N$.
--
--   This is the threshold structure on which the analysis of $JP^U$ and of follow-the-crowd behaviour rests.
--
--   **Formalization Note** The paper writes $\tilde p(p^-) = (1,\dots,1,p_m,0,\dots,0)$ with $m \ge 1$ ones and $p_m\in(0,1]$. Two departures are disclosed. (i) At $u(m,p^-) = 0$ the paper allows any $p_m\in[0,1]$; Assumption 1's tie-break (join when the expected utility gain is non-negative) selects the pure response $p_m = 1$. (ii) The printed form, with at least one $1$ followed by $p_m > 0$, cannot express $(1,0,\dots,0)$, which is the best response when $u(1,p^-) < 0$ (for example when $R/C$ is just above $1/\mu_L$); the threshold here may be $m = 0$.
-- source:
--   Yang, Shang & Liu, Follow the crowd with uncertain service capacity, SSRN 4159035 (version of June 24, 2022), p. 8, Proposition 1 (threshold form, pure best response under Assumption 1; see Formalization Note); proof: Online Appendix p. 1 (PDF 25)

import Mathlib
import Definitions.Def_FollowCrowd_Inference_Model

namespace FollowCrowd.Inference

theorem proposition_1 (P : Params) (hP : P.Standing) (p : ℕ → ℝ) (hp : IsJoinVec p) :
    ∃ m : ℕ, m < Nbar P ∧ (∀ n ≤ m, bestResp P p n = 1) ∧
      ∀ n, m < n → n ≤ Nbar P → bestResp P p n = 0 := by sorry

end FollowCrowd.Inference
