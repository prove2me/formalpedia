-- Prove2me | Theorems.Thm_DIGing_Push_lemma_14
-- name    : DIGing.Push.lemma_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:57:35.889668+00:00
-- url     : https://prove2.me/theorems/3b552621-d00e-45d8-bea2-6328a9bd1c31
-- title:
--   Lemma 14, p. 23 — first arrow q → z: ‖z‖^{λ,K}_F ≤ L(1 + 1/λ)‖q‖^{λ,K}_F
-- statement:
--   Let each $f_i$ satisfy Assumption 4, and let $L=\max_iL_i$. Let $\mathbf x(0),\mathbf x(1),\dots$ be any sequence in $\mathbb R^{n\times p}$ and $x^*\in\mathbb R^p$ any point. Put $\mathbf q(k)=\mathbf x(k)-\mathbf 1(x^*)^\top$, $\mathbf z(k)=\nabla\mathbf f(\mathbf x(k))-\nabla\mathbf f(\mathbf x(k-1))$ for $k\ge1$ and $\mathbf z(0)=0$. Then for every $K=0,1,\dots$ and every $\lambda\in(0,1)$,
--   $$\|\mathbf z\|_F^{\lambda,K}\le L\Big(1+\frac1\lambda\Big)\|\mathbf q\|_F^{\lambda,K}.$$
--
--   This is the first gain $\gamma_1=L(1+1/\lambda)$ of the small gain cycle $\mathbf q\to\mathbf z\to\check{\mathbf h}\to\check{\mathbf x}\to\mathbf q$; the paper restates Lemma 5 for Push-DIGing.
--
--   **Formalization Note** Only Assumption 4 is used, so the sequence is arbitrary (not necessarily a run of the algorithm) and $x^*$ is any point.
-- source:
--   arXiv:1607.03218v3, Lemma 14, p. 23 (restating Lemma 5, p. 10)

import Mathlib
import Definitions.Def_DIGing_Undir_Common
import Definitions.Def_DIGing_Push_Setting

namespace DIGing.Push

theorem lemma_14 {n p : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ) (Lc : Fin n → ℝ)
    (h4 : DIGing.Undir.Assumption4 f Lc) (x : ℕ → DIGing.Undir.Stack n p) (xstar : EuclideanSpace ℝ (Fin p)) :
    ∀ K : ℕ, ∀ lam : ℝ, 0 < lam → lam < 1 →
      DIGing.Undir.ergK lam K (fun k => DIGing.Undir.frob (DIGing.Undir.zSeq f x k)) ≤
        DIGing.Undir.Lmax Lc * (1 + 1 / lam) * DIGing.Undir.ergK lam K (fun k => DIGing.Undir.frob (x k - DIGing.Undir.ones xstar)) := by sorry

end DIGing.Push
