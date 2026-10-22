-- Prove2me | Theorems.Thm_FollowCrowd_Inference_eq_A_1
-- name    : FollowCrowd.Inference.eq_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:17:03.823457+00:00
-- url     : https://prove2.me/theorems/05789d6d-7563-41bb-8c28-a8b38909a0c2
-- title:
--   (A-1), Online Appendix p. 1 — the belief (A-1) equals Bayes' rule (1) at every reachable state; (2)–(3) is a probability law
-- statement:
--   Assume the standing assumptions of the model ($\mu_H > \mu_L > 0$, $\gamma\in(0,1)$, $\lambda > 0$, $C > 0$, $R > C/\mu_L$) and let $p^- = (1, p^-_1, \dots)$ be a joining vector with every $p^-_i \in [0,1]$.
--
--   1. For $X \in \{H, L\}$, the numbers $\pi_X(n,p^-)$ of (2)–(3) are nonnegative and sum to one over $n \in \{0,\dots,\bar N\}$.
--
--   2. For every $n \le \bar N$ with $\prod_{i=0}^{n-1}p^-_i > 0$ (state $n$ has positive probability),
--   $$\theta_n(p^-) = \frac{\gamma\,\pi_H(n,p^-)}{\gamma\,\pi_H(n,p^-) + (1-\gamma)\,\pi_L(n,p^-)},$$
--   that is, the belief defined by (A-1) is the Bayesian posterior (1).
--
--   This ties the closed form (A-1) used throughout to the defining Bayes formula of p. 8.
--
--   **Formalization Note** The model defines $\theta_n$ by (A-1) for every $n$; this statement recovers (1) exactly where (1) is not $0/0$.
-- source:
--   Yang, Shang & Liu, Follow the crowd with uncertain service capacity, SSRN 4159035 (version of June 24, 2022), Online Appendix p. 1 (PDF 25), proof of Lemma 1, (A-1); p. 8, eqs. (1)–(3)

import Mathlib
import Definitions.Def_FollowCrowd_Inference_Model

namespace FollowCrowd.Inference

theorem eq_A_1 (P : Params) (hP : P.Standing) (p : ℕ → ℝ) (hp : IsJoinVec p) :
    (∀ mu ∈ ({P.muH, P.muL} : Set ℝ),
      (∀ n, 0 ≤ stat P mu p n) ∧ ∑ n ∈ Finset.range (Nbar P + 1), stat P mu p n = 1) ∧
    ∀ n ≤ Nbar P, 0 < ∏ i ∈ Finset.range n, p i →
      theta P p n = P.γ * stat P P.muH p n /
        (P.γ * stat P P.muH p n + (1 - P.γ) * stat P P.muL p n) := by sorry

end FollowCrowd.Inference
