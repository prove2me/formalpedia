-- Prove2me | Theorems.Thm_FRBSplitting_Weak_weak_cluster_mem_zeroSet
-- name    : FRBSplitting.Weak.weak_cluster_mem_zeroSet
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:42:47.147965+00:00
-- url     : https://prove2.me/theorems/52506bdd-a15b-483d-a5c8-797dce75d54f
-- title:
--   Proof of Theorem 2.5, p. 7 — every sequential weak cluster point of (x_k) lies in (A+B)⁻¹(0)
-- statement:
--   Let $H$ be a real Hilbert space, $A:H\rightrightarrows H$ maximally monotone, and $B:H\to H$ monotone and $L$-Lipschitz with $L>0$, and suppose $(A+B)^{-1}(0)\ne\varnothing$. Fix $\varepsilon>0$ and step sizes $(\lambda_k)_{k\ge -1}\subseteq[\varepsilon,\tfrac{1-2\varepsilon}{2L}]$, and let $(x_k)_{k\ge-1}$ be generated from arbitrary $x_0,x_{-1}\in H$ by
--
--   $$x_{k+1}=J_{\lambda_k A}\big(x_k-\lambda_k B(x_k)-\lambda_{k-1}(B(x_k)-B(x_{k-1}))\big)\qquad\forall k\in\mathbb N.$$
--
--   Then every sequential weak cluster point $\bar x$ of $(x_k)$ satisfies
--
--   $$0\in(A+B)(\bar x).$$
--
--   This is the step of the proof of Theorem 2.5 that identifies the candidate limits as solutions of (12).
--
--   **Formalization Note.** The resolvent is not constructed: the iteration is driven by a family $J$ with $J(\gamma)=J_{\gamma A}$ for every $\gamma>0$, given as the hypothesis that $\gamma^{-1}(w-J(\gamma)w)\in A(J(\gamma)w)$ for all $w$. The paper's sequences start at $x_{-1}$ and $\lambda_{-1}$; in Lean `x j` is $x_{j-1}$ and `lam j` is $\lambda_{j-1}$, so a statement about $x_{k+1},x_k,x_{k-1},\lambda_k,\lambda_{k-1}$ is stated about `x (k+2)`, `x (k+1)`, `x k`, `lam (k+1)`, `lam k`. A sequential weak cluster point is the weak limit of a subsequence $(x_{\varphi(n)})$ with $\varphi$ strictly increasing.
-- source:
--   Malitsky & Tam, A Forward-Backward Splitting Method for Monotone Inclusions Without Cocoercivity, arXiv:1808.04162v4, p. 7, proof of Theorem 2.5, paragraph after (25)

import Mathlib
import Definitions.Def_ThreeOpSplitting_Accel_MonotoneOperators
import Definitions.Def_FRBSplitting_Weak_Setting
open InnerProductSpace ThreeOpSplitting.Accel

namespace FRBSplitting.Weak

theorem weak_cluster_mem_zeroSet {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H → Set H) (B : H → H) (J : ℝ → H → H) (L ε : ℝ)
    (hA : IsMaximalMonotone A)
    (hJ : IsResolventFamily A J)
    (hBm : IsMonotoneFun B)
    (hL : 0 < L) (hBL : IsLipschitzOp L B)
    (hzer : (zeroSet A B).Nonempty)
    (hε : 0 < ε) (lam : ℕ → ℝ) (hlam : ∀ j, ε ≤ lam j ∧ lam j ≤ (1 - 2 * ε) / (2 * L))
    (x : ℕ → H) (hrun : IsFRBRun J B lam x) :
    ∀ p : H, IsWeakClusterPt x p → p ∈ zeroSet A B := by sorry

end FRBSplitting.Weak
