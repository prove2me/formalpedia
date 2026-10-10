-- Prove2me | Theorems.Thm_FRBSplitting_Inertial_theorem_4_3
-- name    : FRBSplitting.Inertial.theorem_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:43:50.983055+00:00
-- url     : https://prove2.me/theorems/5550e972-dafc-49f1-bd88-600dcd9b98d4
-- title:
--   Theorem 4.3, p. 13 — the relaxed inertial forward-reflected-backward iterates converge weakly to a zero of A + B
-- statement:
--   Let $H$ be a real Hilbert space, $A:H\rightrightarrows H$ maximally monotone, and $B:H\to H$ monotone with $(A+B)^{-1}(0)\ne\varnothing$. Suppose $\alpha\in[0,1)$, $\beta\in(0,1]$, $\lambda>0$ and either
--
--   1. $B$ is $L$-Lipschitz and
--   $$\lambda<\min\Big\{\frac{2-\beta-\alpha\beta-2\alpha}{2L},\frac{1-\alpha-\alpha\beta}{\beta L}\Big\},\qquad(41)$$
--   2. or $B$ is $\tfrac1L$-cocoercive, $\alpha<\frac{2-\beta}{2+\beta}$ and
--   $$\lambda<\min\Big\{\frac{2-\beta-\alpha\beta+2\alpha}{2L},\frac{1-\alpha+\alpha\beta}{\beta L}\Big\}.\qquad(42)$$
--
--   Given $x_0,x_{-1}\in H$, define $(x_k)$ and $(z_k)$ by the relaxed inertial scheme
--
--   $$z_{k+1}=J_{\lambda A}\Big(x_k-\lambda B(x_k)-\frac\lambda\beta\big(B(x_k)-B(x_{k-1})\big)+\frac\alpha\beta(x_k-x_{k-1})\Big),\qquad x_{k+1}=(1-\beta)x_k+\beta z_{k+1}.$$
--
--   Then $(x_k)$ converges weakly to a point of $(A+B)^{-1}(0)$.
--
--   Inertia ($\alpha>0$) and relaxation ($\beta<1$) extend the forward-reflected-backward method of §2, which is the case $\alpha=0$, $\beta=1$; the theorem describes exactly which parameter combinations keep weak convergence, without cocoercivity in case 1.
--
--   **Formalization Note.** The resolvent is supplied as a family `J` with the hypothesis that each `J γ`, $\gamma>0$, is the resolvent of $\gamma A$ (it exists and is unique for maximally monotone $A$). Indices are shifted by one (`x j` is $x_{j-1}$), which does not affect a limit. Weak convergence is $\langle x_k,v\rangle\to\langle\bar x,v\rangle$ for all $v$. "$\tfrac1L$-cocoercive" is $\tfrac1L\|Bx-By\|^2\le\langle Bx-By,x-y\rangle$. $L>0$ is assumed in both cases because (41) and (42) divide by $L$. $B$ is assumed monotone in both cases, as printed.
-- source:
--   Malitsky & Tam, A Forward-Backward Splitting Method for Monotone Inclusions Without Cocoercivity, arXiv:1808.04162v4, p. 13, Theorem 4.3, (41)–(42), with (34) on p. 11

import Mathlib
import Definitions.Def_ThreeOpSplitting_Accel_MonotoneOperators
import Definitions.Def_FRBSplitting_Inertial_Setting
open InnerProductSpace ThreeOpSplitting.Accel

namespace FRBSplitting.Inertial

theorem theorem_4_3 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H → Set H) (B : H → H) (J : ℝ → H → H) (L α β lam : ℝ)
    (hA : IsMaximalMonotone A)
    (hJ : IsResolventFamily A J)
    (hBm : IsMonotoneFun B)
    (hzer : (FRBSplitting.Weak.zeroSet A B).Nonempty)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hlam : 0 < lam) (hL : 0 < L)
    (hcase : (IsLipschitzOp L B ∧
        lam < min ((2 - β - α * β - 2 * α) / (2 * L)) ((1 - α - α * β) / (β * L))) ∨
      (IsCocoercive L⁻¹ B ∧ α < (2 - β) / (2 + β) ∧
        lam < min ((2 - β - α * β + 2 * α) / (2 * L)) ((1 - α + α * β) / (β * L))))
    (x z : ℕ → H) (hrun : IsRelaxedInertialRun J B α β lam x z) :
    ∃ xs ∈ FRBSplitting.Weak.zeroSet A B, FRBSplitting.Weak.IsWeakLimit x xs := by sorry

end FRBSplitting.Inertial
