-- Prove2me | Theorems.Thm_FRBSplitting_Weak_bounded_and_steps_vanish
-- name    : FRBSplitting.Weak.bounded_and_steps_vanish
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:42:38.938756+00:00
-- url     : https://prove2.me/theorems/1808f758-7bc7-4407-a163-72c6af614abe
-- title:
--   Proof of Theorem 2.5, p. 7, first line — (x_k) is bounded and ‖x_k − x_{k+1}‖ → 0
-- statement:
--   Let $H$ be a real inner product space, $A:H\rightrightarrows H$ a monotone operator, and $B:H\to H$ a monotone $L$-Lipschitz operator with $L>0$. Fix $\varepsilon>0$ and step sizes $(\lambda_k)_{k\ge -1}\subseteq[\varepsilon,\tfrac{1-2\varepsilon}{2L}]$, and let $(x_k)_{k\ge-1}$ be generated from arbitrary $x_0,x_{-1}\in H$ by the forward-reflected-backward scheme
--
--   $$x_{k+1}=J_{\lambda_k A}\big(x_k-\lambda_k B(x_k)-\lambda_{k-1}(B(x_k)-B(x_{k-1}))\big)\qquad\forall k\in\mathbb N.$$
--
--   Suppose moreover that $(A+B)^{-1}(0)\neq\varnothing$. Then $(x_k)$ is bounded and
--
--   $$\lim_{k\to\infty}\|x_k-x_{k+1}\|=0.$$
--
--   Boundedness provides weak cluster points, and asymptotic regularity lets one pass to the limit in the inclusion (25).
--
--   **Formalization Note.** The resolvent is not constructed: the iteration is driven by a family $J$ with $J(\gamma)=J_{\gamma A}$ for every $\gamma>0$, given as the hypothesis that $\gamma^{-1}(w-J(\gamma)w)\in A(J(\gamma)w)$ for all $w$. The paper's sequences start at $x_{-1}$ and $\lambda_{-1}$; in Lean `x j` is $x_{j-1}$ and `lam j` is $\lambda_{j-1}$, so a statement about $x_{k+1},x_k,x_{k-1},\lambda_k,\lambda_{k-1}$ is stated about `x (k+2)`, `x (k+1)`, `x k`, `lam (k+1)`, `lam k`. $A$ is only assumed monotone and $H$ need not be complete (stronger than the page's setting).
-- source:
--   Malitsky & Tam, A Forward-Backward Splitting Method for Monotone Inclusions Without Cocoercivity, arXiv:1808.04162v4, p. 7, proof of Theorem 2.5, first line

import Mathlib
import Definitions.Def_ThreeOpSplitting_Accel_MonotoneOperators
import Definitions.Def_FRBSplitting_Weak_Setting
open InnerProductSpace ThreeOpSplitting.Accel

namespace FRBSplitting.Weak

theorem bounded_and_steps_vanish {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : H → Set H) (B : H → H) (J : ℝ → H → H) (L ε : ℝ)
    (hA : IsMonotoneOp A)
    (hJ : IsResolventFamily A J)
    (hBm : IsMonotoneFun B)
    (hL : 0 < L) (hBL : IsLipschitzOp L B)
    (hε : 0 < ε) (lam : ℕ → ℝ) (hlam : ∀ j, ε ≤ lam j ∧ lam j ≤ (1 - 2 * ε) / (2 * L))
    (x : ℕ → H) (hrun : IsFRBRun J B lam x)
    (hzer : (zeroSet A B).Nonempty) :
    Bornology.IsBounded (Set.range x) ∧
      Filter.Tendsto (fun k => ‖x k - x (k + 1)‖) Filter.atTop (nhds 0) := by sorry

end FRBSplitting.Weak
