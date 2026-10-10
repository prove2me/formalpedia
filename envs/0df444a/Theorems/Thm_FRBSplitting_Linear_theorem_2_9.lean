-- Prove2me | Theorems.Thm_FRBSplitting_Linear_theorem_2_9
-- name    : FRBSplitting.Linear.theorem_2_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:44:14.309717+00:00
-- url     : https://prove2.me/theorems/ca296cd8-380c-4918-b626-2454708a4132
-- title:
--   Theorem 2.9, p. 8 — for strongly monotone A the forward-reflected-backward method converges R-linearly to the unique zero of A + B
-- statement:
--   Let $H$ be a real Hilbert space. Let $A:H\rightrightarrows H$ be maximally monotone and $m$-strongly monotone ($m>0$, $\langle x-y,u-v\rangle\ge m\|x-y\|^2$ whenever $u\in A(x)$, $v\in A(y)$), with resolvents $J_{\gamma A}=(I+\gamma A)^{-1}$, $\gamma>0$. Let $B:H\to H$ be monotone and $L$-Lipschitz, $L>0$, and suppose $(A+B)^{-1}(0)\neq\varnothing$. Let $\lambda\in(0,\tfrac1{2L})$. Given $x_0,x_{-1}\in H$, define $(x_k)$ by
--   $$x_{k+1}=J_{\lambda A}\big(x_k-2\lambda B(x_k)+\lambda B(x_{k-1})\big)\qquad\forall k\in\mathbb N.$$
--   Then $(A+B)^{-1}(0)=\{\bar x\}$ for a single point $\bar x$, and $(x_k)$ converges R-linearly to $\bar x$: there are $q\in(0,1)$ and $M\in\mathbb R$ such that
--   $$\|x_k-\bar x\|\le M\,q^k\qquad\text{for all }k .$$
--
--   This is the linear-convergence result for the forward-reflected-backward method: when the set-valued part $A$ is strongly monotone, the method needs neither cocoercivity of $B$ nor a second forward evaluation to converge at a geometric rate.
--
--   **Formalization Note.** Indices are shifted by one: Lean's `x k` is $x_{k-1}$ (so `x 0` $=x_{-1}$), which only rescales $M$; the bound covers the initial point $x_{-1}$ as well. The resolvent is a hypothesis: `J` is any family with `J γ` a resolvent of $A$ for every $\gamma>0$; for maximally monotone $A$ such a family exists (Minty) and is unique. "R-linearly" is not defined in the paper; it is stated as the existence of a geometric bound $Mq^k$ with $q<1$, as the proof gives. $L>0$ is pinned because the step range divides by $L$.
-- source:
--   Malitsky & Tam, A Forward-Backward Splitting Method for Monotone Inclusions Without Cocoercivity, arXiv:1808.04162v4, p. 8, Theorem 2.9

import Mathlib
import Definitions.Def_ThreeOpSplitting_Accel_MonotoneOperators
import Definitions.Def_FRBSplitting_Linear_Setting
open InnerProductSpace ThreeOpSplitting.Accel

namespace FRBSplitting.Linear

theorem theorem_2_9 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H → Set H) (B : H → H) (J : ℝ → H → H) (m L lam : ℝ)
    (hA : IsMaximalMonotone A)
    (hm : 0 < m) (hAs : IsStronglyMonotoneOp m A)
    (hJ : IsResolventFamily A J)
    (hBm : IsMonotoneFun B)
    (hL : 0 < L) (hBL : IsLipschitzOp L B)
    (hzer : (FRBSplitting.Weak.zeroSet A B).Nonempty)
    (hlam0 : 0 < lam) (hlam1 : lam < 1 / (2 * L))
    (x : ℕ → H) (hrun : FRBSplitting.Weak.IsFRBRun J B (fun _ => lam) x) :
    ∃ xs : H, FRBSplitting.Weak.zeroSet A B = {xs} ∧
      ∃ q M : ℝ, 0 < q ∧ q < 1 ∧ ∀ k : ℕ, ‖x k - xs‖ ≤ M * q ^ k := by sorry

end FRBSplitting.Linear
