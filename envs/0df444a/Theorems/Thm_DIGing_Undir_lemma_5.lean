-- Prove2me | Theorems.Thm_DIGing_Undir_lemma_5
-- name    : DIGing.Undir.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:09:57.797276+00:00
-- url     : https://prove2.me/theorems/e0b1a023-2494-46ea-b1e9-80aff5df2276
-- title:
--   Lemma 5, p. 10 — first arrow q → z: ‖z‖^{λ,K}_F ≤ L(1 + 1/λ)‖q‖^{λ,K}_F
-- statement:
--   Let each $f_i$ satisfy Assumption 4 with constants $L_i$, and let $L=\max_iL_i$. Let $\mathbf x(0),\mathbf x(1),\dots$ be any sequence of $n\times p$ matrices, $x^*\in\mathbb R^p$ any point, $\mathbf q(k)=\mathbf x(k)-\mathbf 1(x^*)^\top$, and $\mathbf z(k)=\nabla\mathbf f(\mathbf x(k))-\nabla\mathbf f(\mathbf x(k-1))$ for $k\ge1$, $\mathbf z(0)=0$. Then for every $K=0,1,\dots$ and every $\lambda\in(0,1)$,
--   $$\|\mathbf z\|_F^{\lambda,K}\le L\Big(1+\frac1\lambda\Big)\|\mathbf q\|_F^{\lambda,K}.$$
--
--   This is the first arrow of the cycle $\mathbf q\to\mathbf z\to\check{\mathbf y}\to\check{\mathbf x}\to\mathbf q$ to which the small gain theorem is applied: successive gradient differences are controlled by the distance to the optimum.
--
--   **Formalization Note.** The statement uses only the Lipschitz bound, so it is stated for an arbitrary sequence $\mathbf x$ and an arbitrary point $x^*$, without the DIGing recursion, Assumption 5 or optimality of $x^*$ (all dropped; the statement is stronger).
-- source:
--   Nedić, Olshevsky & Shi, arXiv:1607.03218v3, Lemma 5, p. 10 (q and z defined in §3.2, p. 10)

import Mathlib
import Definitions.Def_DIGing_Undir_Common
import Definitions.Def_DIGing_Undir_Setting

namespace DIGing.Undir

theorem lemma_5 {n p : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ) (Lc : Fin n → ℝ)
    (h4 : Assumption4 f Lc) (x : ℕ → Stack n p) (xstar : EuclideanSpace ℝ (Fin p)) :
    ∀ K : ℕ, ∀ lam : ℝ, 0 < lam → lam < 1 →
      ergK lam K (fun k => frob (zSeq f x k)) ≤
        Lmax Lc * (1 + 1 / lam) * ergK lam K (fun k => frob (x k - ones xstar)) := by sorry

end DIGing.Undir
