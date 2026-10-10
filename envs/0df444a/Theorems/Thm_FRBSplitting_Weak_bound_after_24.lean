-- Prove2me | Theorems.Thm_FRBSplitting_Weak_bound_after_24
-- name    : FRBSplitting.Weak.bound_after_24
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:42:42.953524+00:00
-- url     : https://prove2.me/theorems/f60faf80-76a9-4501-83ba-12763f44fbfa
-- title:
--   Proof of Theorem 2.5, p. 6, display after (24) — ½‖x_{k+1} − x‖² + ε Σ‖x_{i+1} − x_i‖² ≤ initial energy
-- statement:
--   Let $H$ be a real inner product space, $A:H\rightrightarrows H$ a monotone operator, and $B:H\to H$ a monotone $L$-Lipschitz operator with $L>0$. Fix $\varepsilon>0$ and step sizes $(\lambda_k)_{k\ge -1}\subseteq[\varepsilon,\tfrac{1-2\varepsilon}{2L}]$, and let $(x_k)_{k\ge-1}$ be generated from arbitrary $x_0,x_{-1}\in H$ by the forward-reflected-backward scheme
--
--   $$x_{k+1}=J_{\lambda_k A}\big(x_k-\lambda_k B(x_k)-\lambda_{k-1}(B(x_k)-B(x_{k-1}))\big)\qquad\forall k\in\mathbb N.$$
--
--   Then for every $x\in(A+B)^{-1}(0)$ and every $k\in\mathbb N$,
--
--   $$\tfrac12\|x_{k+1}-x\|^2+\varepsilon\sum_{i=0}^{k}\|x_{i+1}-x_i\|^2\le\|x_0-x\|^2+2\lambda_{-1}\langle B(x_0)-B(x_{-1}),x-x_0\rangle+\tfrac12\|x_0-x_{-1}\|^2.$$
--
--   The bound gives boundedness of the iterates and summability of the squared steps.
--
--   **Formalization Note.** The resolvent is not constructed: the iteration is driven by a family $J$ with $J(\gamma)=J_{\gamma A}$ for every $\gamma>0$, given as the hypothesis that $\gamma^{-1}(w-J(\gamma)w)\in A(J(\gamma)w)$ for all $w$. The paper's sequences start at $x_{-1}$ and $\lambda_{-1}$; in Lean `x j` is $x_{j-1}$ and `lam j` is $\lambda_{j-1}$, so a statement about $x_{k+1},x_k,x_{k-1},\lambda_k,\lambda_{k-1}$ is stated about `x (k+2)`, `x (k+1)`, `x k`, `lam (k+1)`, `lam k`. The sum runs over `Finset.range (k+1)` of `‖x (i+2) - x (i+1)‖^2`, i.e. $\sum_{i=0}^k\|x_{i+1}-x_i\|^2$. $A$ is only assumed monotone and $H$ need not be complete (stronger than the page's setting).
-- source:
--   Malitsky & Tam, A Forward-Backward Splitting Method for Monotone Inclusions Without Cocoercivity, arXiv:1808.04162v4, p. 6, proof of Theorem 2.5, display after (24)

import Mathlib
import Definitions.Def_ThreeOpSplitting_Accel_MonotoneOperators
import Definitions.Def_FRBSplitting_Weak_Setting
open InnerProductSpace ThreeOpSplitting.Accel

namespace FRBSplitting.Weak

theorem bound_after_24 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : H → Set H) (B : H → H) (J : ℝ → H → H) (L ε : ℝ)
    (hA : IsMonotoneOp A)
    (hJ : IsResolventFamily A J)
    (hBm : IsMonotoneFun B)
    (hL : 0 < L) (hBL : IsLipschitzOp L B)
    (hε : 0 < ε) (lam : ℕ → ℝ) (hlam : ∀ j, ε ≤ lam j ∧ lam j ≤ (1 - 2 * ε) / (2 * L))
    (x : ℕ → H) (hrun : IsFRBRun J B lam x)
    (xs : H) (hxs : xs ∈ zeroSet A B) :
    ∀ k : ℕ, 1 / 2 * ‖x (k + 2) - xs‖ ^ 2
        + ε * ∑ i ∈ Finset.range (k + 1), ‖x (i + 2) - x (i + 1)‖ ^ 2
      ≤ ‖x 1 - xs‖ ^ 2 + 2 * lam 0 * ⟪B (x 1) - B (x 0), xs - x 1⟫_ℝ + 1 / 2 * ‖x 1 - x 0‖ ^ 2 := by sorry

end FRBSplitting.Weak
