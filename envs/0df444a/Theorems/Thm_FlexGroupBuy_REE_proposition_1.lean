-- Prove2me | Theorems.Thm_FlexGroupBuy_REE_proposition_1
-- name    : FlexGroupBuy.REE.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:21:41.650828+00:00
-- url     : https://prove2.me/theorems/3263371e-fd04-4ce8-9973-fdff471f4c08
-- title:
--   Proposition 1, p. 13 — for θ > 1 no campaign in which low-end customers sign up first satisfies the IR/IC constraints
-- statement:
--   Assume the standing assumptions $H>L>0$, $0<\gamma<1$, $\lambda>0$, $c>0$, $\theta>1$, and let $N\ge 1$. In **Case II** low-end customers sign up first and both segments sign up from the tipping state $\bar x^G\in[0,N)$ on; the expected waiting time is $w^{II}(n)=(n-1)/\lambda$ for $n\le \bar x^G$ and $\bar x^G/\lambda+(n-\bar x^G-1)/((1-\gamma)\lambda)$ for $n>\bar x^G$. Then for no prices $p^G,r^G$ do the six constraints
--   $$
--   \begin{aligned}
--   &IR_L:\ \theta L-p^G-c\,w^{II}(n)\ge 0, && ICL:\ \theta L-p^G-c\,w^{II}(n)\ge L-r^G, && 1\le n\le N,\\
--   &IR_{H1}:\ H-r^G\ge 0, && IC_{H1}:\ H-r^G\ge \theta H-p^G-c\,w^{II}(n), && \bar x^G<n\le N,\\
--   &IR_{H2}:\ \theta H-p^G-c\,w^{II}(n)\ge 0, && IC_{H2}:\ \theta H-p^G-c\,w^{II}(n)\ge H-r^G, && 1\le n\le \bar x^G,
--   \end{aligned}
--   $$
--   all hold, over integer states $n$.
--
--   Together with Lemma A.1 this is Proposition 1: with $\theta>1$ the equilibrium segmentation is one of $\{H\}$, $\{H;H+L\}$, $\{H+L\}$ (Case I), since the low-end-first scenarios $\{L\}$ ($\bar x^G=0$) and $\{L;H+L\}$ ($0<\bar x^G<N$) cannot occur.
--
--   **Formalization Note.** The statement is the infeasibility of Case II that the printed proof establishes (Online Appendix pp. 2–3), not the full classification sentence. The scenario $\{L+H\}$ coincides with Case I's $\bar x^G=N$ and is excluded from Case II as on the page.
-- source:
--   Hu, Liu & Zhai, Intertemporal Segmentation via Flexible-Duration Group Buying, SSRN 3242687 (version of 2019-12-06; MSOM forthcoming), p. 13, Proposition 1; proof Online Appendix pp. 2–3

import Mathlib
import Definitions.Def_FlexGroupBuy_REE_Model

namespace FlexGroupBuy.REE

/-- Proposition 1 (p. 13), in the form its proof establishes (Online Appendix pp. 2–3): for `θ > 1`
no tipping state `x ∈ [0, N)` and no prices `p`, `r` satisfy the six IR/IC constraints of
Case II (low-end customers sign up first), with the Case II waiting time `wII`. -/
theorem proposition_1 (P : Params) (hP : P.Standing) (N : ℕ) (hN : 1 ≤ N)
    (x : ℝ) (hx0 : 0 ≤ x) (hxN : x < N) (p r : ℝ) :
    ¬ ((∀ n : ℕ, 1 ≤ n → n ≤ N → P.theta * P.L - p - P.c * wII P x n ≥ 0) ∧
       (∀ n : ℕ, 1 ≤ n → n ≤ N → P.theta * P.L - p - P.c * wII P x n ≥ P.L - r) ∧
       (∀ n : ℕ, x < (n : ℝ) → n ≤ N → P.H - r ≥ 0) ∧
       (∀ n : ℕ, x < (n : ℝ) → n ≤ N → P.H - r ≥ P.theta * P.H - p - P.c * wII P x n) ∧
       (∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ x → P.theta * P.H - p - P.c * wII P x n ≥ 0) ∧
       (∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ x → P.theta * P.H - p - P.c * wII P x n ≥ P.H - r)) := by sorry

end FlexGroupBuy.REE
