-- Prove2me | Theorems.Thm_FRBSplitting_Weak_eq_26
-- name    : FRBSplitting.Weak.eq_26
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:42:59.53915+00:00
-- url     : https://prove2.me/theorems/e6a239ef-9be5-4d85-a73d-3d323e00a3ca
-- title:
--   (26), proof of Theorem 2.5, p. 7 — the energy ‖x_k − x‖² + 2λ_{k−1}⟨B(x_k) − B(x_{k−1}), x − x_k⟩ + ½‖x_k − x_{k−1}‖² converges
-- statement:
--   Let $H$ be a real inner product space, $A:H\rightrightarrows H$ a monotone operator, and $B:H\to H$ a monotone $L$-Lipschitz operator with $L>0$. Fix $\varepsilon>0$ and step sizes $(\lambda_k)_{k\ge -1}\subseteq[\varepsilon,\tfrac{1-2\varepsilon}{2L}]$, and let $(x_k)_{k\ge-1}$ be generated from arbitrary $x_0,x_{-1}\in H$ by the forward-reflected-backward scheme
--
--   $$x_{k+1}=J_{\lambda_k A}\big(x_k-\lambda_k B(x_k)-\lambda_{k-1}(B(x_k)-B(x_{k-1}))\big)\qquad\forall k\in\mathbb N.$$
--
--   Then for every $x\in(A+B)^{-1}(0)$ the limit
--
--   $$\lim_{k\to\infty}\Big(\|x_k-x\|^2+2\lambda_{k-1}\langle B(x_k)-B(x_{k-1}),x-x_k\rangle+\tfrac12\|x_k-x_{k-1}\|^2\Big)$$
--
--   exists in $\mathbb R$.
--
--   This is the convergence of the Lyapunov energy of Lemma 2.4.
--
--   **Formalization Note.** The resolvent is not constructed: the iteration is driven by a family $J$ with $J(\gamma)=J_{\gamma A}$ for every $\gamma>0$, given as the hypothesis that $\gamma^{-1}(w-J(\gamma)w)\in A(J(\gamma)w)$ for all $w$. The paper's sequences start at $x_{-1}$ and $\lambda_{-1}$; in Lean `x j` is $x_{j-1}$ and `lam j` is $\lambda_{j-1}$, so a statement about $x_{k+1},x_k,x_{k-1},\lambda_k,\lambda_{k-1}$ is stated about `x (k+2)`, `x (k+1)`, `x k`, `lam (k+1)`, `lam k`. The page states the limit for the cluster point $\bar x$, which by the preceding step is a zero; the Lean statement asserts it for every zero, which is stronger. $A$ is only assumed monotone and $H$ need not be complete.
-- source:
--   Malitsky & Tam, A Forward-Backward Splitting Method for Monotone Inclusions Without Cocoercivity, arXiv:1808.04162v4, p. 7, proof of Theorem 2.5, (26)

import Mathlib
import Definitions.Def_ThreeOpSplitting_Accel_MonotoneOperators
import Definitions.Def_FRBSplitting_Weak_Setting
open InnerProductSpace ThreeOpSplitting.Accel

namespace FRBSplitting.Weak

theorem eq_26 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : H → Set H) (B : H → H) (J : ℝ → H → H) (L ε : ℝ)
    (hA : IsMonotoneOp A)
    (hJ : IsResolventFamily A J)
    (hBm : IsMonotoneFun B)
    (hL : 0 < L) (hBL : IsLipschitzOp L B)
    (hε : 0 < ε) (lam : ℕ → ℝ) (hlam : ∀ j, ε ≤ lam j ∧ lam j ≤ (1 - 2 * ε) / (2 * L))
    (x : ℕ → H) (hrun : IsFRBRun J B lam x) :
    ∀ xs ∈ zeroSet A B, ∃ l : ℝ, Filter.Tendsto
      (fun k => ‖x (k + 1) - xs‖ ^ 2 + 2 * lam k * ⟪B (x (k + 1)) - B (x k), xs - x (k + 1)⟫_ℝ + 1 / 2 * ‖x (k + 1) - x k‖ ^ 2)
      Filter.atTop (nhds l) := by sorry

end FRBSplitting.Weak
