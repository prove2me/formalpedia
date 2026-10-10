-- Prove2me | Theorems.Thm_FRBSplitting_Weak_lemma_2_4
-- name    : FRBSplitting.Weak.lemma_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:42:46.360347+00:00
-- url     : https://prove2.me/theorems/c8263e2b-1482-44ac-b759-8860c01c4519
-- title:
--   Lemma 2.4, p. 5 — the energy inequality (20) for x ∈ (A+B)⁻¹(0)
-- statement:
--   Let $H$ be a real inner product space, $A:H\rightrightarrows H$ a monotone operator, and $B:H\to H$ a monotone $L$-Lipschitz operator with $L>0$. Fix $\varepsilon>0$ and step sizes $(\lambda_k)_{k\ge -1}\subseteq[\varepsilon,\tfrac{1-2\varepsilon}{2L}]$, and let $(x_k)_{k\ge-1}$ be generated from arbitrary $x_0,x_{-1}\in H$ by the forward-reflected-backward scheme
--
--   $$x_{k+1}=J_{\lambda_k A}\big(x_k-\lambda_k B(x_k)-\lambda_{k-1}(B(x_k)-B(x_{k-1}))\big)\qquad\forall k\in\mathbb N.$$
--
--   Then for every $x\in(A+B)^{-1}(0)$ and every $k\in\mathbb N$,
--
--   $$\|x_{k+1}-x\|^2+2\lambda_k\langle B(x_{k+1})-B(x_k),x-x_{k+1}\rangle+\big(\tfrac12+\varepsilon\big)\|x_{k+1}-x_k\|^2\le\|x_k-x\|^2+2\lambda_{k-1}\langle B(x_k)-B(x_{k-1}),x-x_k\rangle+\tfrac12\|x_k-x_{k-1}\|^2.$$
--
--   This is the Lyapunov-type descent inequality that drives the convergence proof of Theorem 2.5.
--
--   **Formalization Note.** The resolvent is not constructed: the iteration is driven by a family $J$ with $J(\gamma)=J_{\gamma A}$ for every $\gamma>0$, given as the hypothesis that $\gamma^{-1}(w-J(\gamma)w)\in A(J(\gamma)w)$ for all $w$. The paper's sequences start at $x_{-1}$ and $\lambda_{-1}$; in Lean `x j` is $x_{j-1}$ and `lam j` is $\lambda_{j-1}$, so a statement about $x_{k+1},x_k,x_{k-1},\lambda_k,\lambda_{k-1}$ is stated about `x (k+2)`, `x (k+1)`, `x k`, `lam (k+1)`, `lam k`. The step range includes $\lambda_{-1}$ (the paper's sequence starts at $k=-1$). Relative to the page, maximal monotonicity of $A$ is weakened to monotonicity and completeness of $H$ is not assumed; both drops make the statement stronger. $L>0$ is assumed because the step range divides by $L$.
-- source:
--   Malitsky & Tam, A Forward-Backward Splitting Method for Monotone Inclusions Without Cocoercivity, arXiv:1808.04162v4, p. 5, Lemma 2.4, (20)

import Mathlib
import Definitions.Def_ThreeOpSplitting_Accel_MonotoneOperators
import Definitions.Def_FRBSplitting_Weak_Setting
open InnerProductSpace ThreeOpSplitting.Accel

namespace FRBSplitting.Weak

theorem lemma_2_4 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : H → Set H) (B : H → H) (J : ℝ → H → H) (L ε : ℝ)
    (hA : IsMonotoneOp A)
    (hJ : IsResolventFamily A J)
    (hBm : IsMonotoneFun B)
    (hL : 0 < L) (hBL : IsLipschitzOp L B)
    (hε : 0 < ε) (lam : ℕ → ℝ) (hlam : ∀ j, ε ≤ lam j ∧ lam j ≤ (1 - 2 * ε) / (2 * L))
    (x : ℕ → H) (hrun : IsFRBRun J B lam x)
    (xs : H) (hxs : xs ∈ zeroSet A B) :
    ∀ k : ℕ, ‖x (k + 2) - xs‖ ^ 2 + 2 * lam (k + 1) * ⟪B (x (k + 2)) - B (x (k + 1)), xs - x (k + 2)⟫_ℝ
        + (1 / 2 + ε) * ‖x (k + 2) - x (k + 1)‖ ^ 2
      ≤ ‖x (k + 1) - xs‖ ^ 2 + 2 * lam k * ⟪B (x (k + 1)) - B (x k), xs - x (k + 1)⟫_ℝ
        + 1 / 2 * ‖x (k + 1) - x k‖ ^ 2 := by sorry

end FRBSplitting.Weak
