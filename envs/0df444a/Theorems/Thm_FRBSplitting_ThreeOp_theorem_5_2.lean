-- Prove2me | Theorems.Thm_FRBSplitting_ThreeOp_theorem_5_2
-- name    : FRBSplitting.ThreeOp.theorem_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:45:00.046004+00:00
-- url     : https://prove2.me/theorems/1fd98c63-bc68-40da-9997-1c0babfc6d39
-- title:
--   Theorem 5.2, p. 16 — the three-operator forward-reflected-backward scheme converges weakly to a zero of A + B + C
-- statement:
--   Let $H$ be a real Hilbert space. Let $A:H\rightrightarrows H$ be maximally monotone, with resolvents $J_{\gamma A}=(I+\gamma A)^{-1}$; let $B:H\to H$ be monotone and $L_1$-Lipschitz ($L_1\ge0$); and let $C:H\to H$ be $\tfrac1{L_2}$-cocoercive ($L_2>0$). Suppose that $(A+B+C)^{-1}(0)\neq\varnothing$ and
--
--   $$0<\lambda<\frac{2}{4L_1+L_2}.$$
--
--   Given $x_0,x_{-1}\in H$, define the sequence $(x_k)$ by
--
--   $$x_{k+1}=J_{\lambda A}\big(x_k-2\lambda B(x_k)+\lambda B(x_{k-1})-\lambda C(x_k)\big)\qquad\forall k\in\mathbb N.$$
--
--   Then $(x_k)$ converges weakly to a point of $(A+B+C)^{-1}(0)$.
--
--   The scheme uses one resolvent of $A$, one new evaluation of $B$ and one evaluation of $C$ per iteration. Treating $B+C$ as a single $(L_1+L_2)$-Lipschitz operator in the two-operator forward-reflected-backward method would require $\lambda<1/(2L_1+2L_2)$; exploiting the cocoercivity of $C$ enlarges the admissible range to $\lambda<1/(2L_1+\tfrac12L_2)$.
--
--   **Formalization Note.** The resolvent is a hypothesis: a family `J : ℝ → H → H` with `IsResolventFamily A J`; for a maximally monotone $A$ such a family exists (Minty's theorem) and is unique on $\gamma>0$. "$\tfrac1{L_2}$-cocoercive" is `IsCocoercive L₂⁻¹ C` with $L_2>0$, and the Lipschitz constant carries its sign $L_1\ge0$ ($L_1=0$ allowed). The zero set is $\{x : -(B+C)(x)\in A(x)\}$. Indices are shifted by one: Lean's `x j` is $x_{j-1}$, and the initial points `x 0`, `x 1` are arbitrary. Weak convergence is stated through inner products: $\langle x_k,v\rangle\to\langle\bar x,v\rangle$ for all $v\in H$.
-- source:
--   Malitsky & Tam, A Forward-Backward Splitting Method for Monotone Inclusions Without Cocoercivity, arXiv:1808.04162v4, p. 16, Theorem 5.2

import Mathlib
import Definitions.Def_ThreeOpSplitting_Accel_MonotoneOperators
import Definitions.Def_FRBSplitting_ThreeOp_Setting
open InnerProductSpace ThreeOpSplitting.Accel

namespace FRBSplitting.ThreeOp

theorem theorem_5_2 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H → Set H) (B C : H → H) (J : ℝ → H → H) (L₁ L₂ lam : ℝ)
    (hA : IsMaximalMonotone A)
    (hJ : IsResolventFamily A J)
    (hBm : IsMonotoneFun B)
    (hL₁ : 0 ≤ L₁) (hBL : IsLipschitzOp L₁ B)
    (hL₂ : 0 < L₂) (hC : IsCocoercive L₂⁻¹ C)
    (hzer : (FRBSplitting.Weak.zeroSet A (fun y => B y + C y)).Nonempty)
    (hlam0 : 0 < lam) (hlam1 : lam < 2 / (4 * L₁ + L₂))
    (x : ℕ → H) (hrun : IsThreeOpRun J B C lam x) :
    ∃ xs ∈ FRBSplitting.Weak.zeroSet A (fun y => B y + C y), FRBSplitting.Weak.IsWeakLimit x xs := by sorry

end FRBSplitting.ThreeOp
