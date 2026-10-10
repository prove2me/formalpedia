-- Prove2me | Theorems.Thm_FRBSplitting_Weak_theorem_2_5
-- name    : FRBSplitting.Weak.theorem_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:42:40.44293+00:00
-- url     : https://prove2.me/theorems/3721ce8c-bacb-46ac-b78a-7be6f5b91e9c
-- title:
--   Theorem 2.5, p. 6 — the forward-reflected-backward iterates converge weakly to a zero of A + B
-- statement:
--   Let $H$ be a real Hilbert space, $A:H\rightrightarrows H$ maximally monotone, and $B:H\to H$ monotone and $L$-Lipschitz with $L>0$, and suppose $(A+B)^{-1}(0)\ne\varnothing$. Fix $\varepsilon>0$ and step sizes $(\lambda_k)_{k\ge -1}\subseteq[\varepsilon,\tfrac{1-2\varepsilon}{2L}]$, and let $(x_k)_{k\ge-1}$ be generated from arbitrary $x_0,x_{-1}\in H$ by
--
--   $$x_{k+1}=J_{\lambda_k A}\big(x_k-\lambda_k B(x_k)-\lambda_{k-1}(B(x_k)-B(x_{k-1}))\big)\qquad\forall k\in\mathbb N.$$
--
--   Then $(x_k)$ converges weakly to a point of $(A+B)^{-1}(0)$: there is $\bar x$ with $0\in A(\bar x)+B(\bar x)$ and
--
--   $$x_k\rightharpoonup\bar x\qquad(k\to\infty).$$
--
--   This is the main convergence result for the forward-reflected-backward method: one forward evaluation of $B$ and one resolvent of $A$ per iteration suffice, with $B$ only monotone and Lipschitz (not cocoercive).
--
--   **Formalization Note.** The resolvent is not constructed: the iteration is driven by a family $J$ with $J(\gamma)=J_{\gamma A}$ for every $\gamma>0$, given as the hypothesis that $\gamma^{-1}(w-J(\gamma)w)\in A(J(\gamma)w)$ for all $w$. The paper's sequences start at $x_{-1}$ and $\lambda_{-1}$; in Lean `x j` is $x_{j-1}$ and `lam j` is $\lambda_{j-1}$, so a statement about $x_{k+1},x_k,x_{k-1},\lambda_k,\lambda_{k-1}$ is stated about `x (k+2)`, `x (k+1)`, `x k`, `lam (k+1)`, `lam k`. Maximal monotonicity of $A$ is kept as a hypothesis alongside the resolvent family. $L>0$ is assumed because the step range divides by $L$. The step range constrains every $\lambda_j$, $j\ge-1$.
-- source:
--   Malitsky & Tam, A Forward-Backward Splitting Method for Monotone Inclusions Without Cocoercivity, arXiv:1808.04162v4, p. 6, Theorem 2.5

import Mathlib
import Definitions.Def_ThreeOpSplitting_Accel_MonotoneOperators
import Definitions.Def_FRBSplitting_Weak_Setting
open InnerProductSpace ThreeOpSplitting.Accel

namespace FRBSplitting.Weak

theorem theorem_2_5 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H → Set H) (B : H → H) (J : ℝ → H → H) (L ε : ℝ)
    (hA : IsMaximalMonotone A)
    (hJ : IsResolventFamily A J)
    (hBm : IsMonotoneFun B)
    (hL : 0 < L) (hBL : IsLipschitzOp L B)
    (hzer : (zeroSet A B).Nonempty)
    (hε : 0 < ε) (lam : ℕ → ℝ) (hlam : ∀ j, ε ≤ lam j ∧ lam j ≤ (1 - 2 * ε) / (2 * L))
    (x : ℕ → H) (hrun : IsFRBRun J B lam x) :
    ∃ xs ∈ zeroSet A B, IsWeakLimit x xs := by sorry

end FRBSplitting.Weak
