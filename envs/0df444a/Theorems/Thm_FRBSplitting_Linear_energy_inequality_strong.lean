-- Prove2me | Theorems.Thm_FRBSplitting_Linear_energy_inequality_strong
-- name    : FRBSplitting.Linear.energy_inequality_strong
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:44:06.346281+00:00
-- url     : https://prove2.me/theorems/61fe0795-aec1-45b6-8e85-c11aa586ba7f
-- title:
--   Proof of Theorem 2.9, p. 8 — the energy inequality with the factor 1 + 2mλ for m-strongly monotone A
-- statement:
--   Let $H$ be a real inner product space, $A:H\rightrightarrows H$ $m$-strongly monotone with $m>0$, i.e. $\langle x-y,u-v\rangle\ge m\|x-y\|^2$ whenever $u\in A(x)$, $v\in A(y)$, and let $J_\gamma$ be the resolvent $J_{\gamma A}$ of $A$ for every $\gamma>0$. Let $B:H\to H$ be monotone and $L$-Lipschitz with $L>0$, and $\lambda\in(0,\tfrac1{2L})$. Let $(x_k)_{k\ge-1}$ satisfy
--   $$x_{k+1}=J_{\lambda A}\big(x_k-2\lambda B(x_k)+\lambda B(x_{k-1})\big)\qquad\forall k\in\mathbb N,$$
--   and let $x\in(A+B)^{-1}(0)$. Then for every $k\in\mathbb N$
--   $$(1+2m\lambda)\|x_{k+1}-x\|^2+2\lambda\langle B(x_{k+1})-B(x_k),x-x_{k+1}\rangle+(1-\lambda L)\|x_{k+1}-x_k\|^2\le\|x_k-x\|^2+2\lambda\langle B(x_k)-B(x_{k-1}),x-x_k\rangle+\tfrac12\|x_k-x_{k-1}\|^2 .$$
--
--   This is the strongly monotone counterpart of the energy inequality of Lemma 2.4: strong monotonicity of $A$ contributes the extra term $2m\lambda\|x_{k+1}-x\|^2$, which drives the linear rate.
--
--   **Formalization Note.** Indices are shifted by one (Lean's `x (k+2)`, `x (k+1)`, `x k` are $x_{k+1},x_k,x_{k-1}$). The resolvent is a hypothesis: `J` is any family with `J γ` a resolvent of $A$ for every $\gamma>0$. Maximal monotonicity of $A$ and completeness of $H$ are not needed for this inequality and are dropped (a stronger statement); $L>0$ is pinned because the step range $(0,\tfrac1{2L})$ divides by $L$.
-- source:
--   Malitsky & Tam, A Forward-Backward Splitting Method for Monotone Inclusions Without Cocoercivity, arXiv:1808.04162v4, p. 8, proof of Theorem 2.9, first display

import Mathlib
import Definitions.Def_ThreeOpSplitting_Accel_MonotoneOperators
import Definitions.Def_FRBSplitting_Linear_Setting
open InnerProductSpace ThreeOpSplitting.Accel

namespace FRBSplitting.Linear

theorem energy_inequality_strong {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : H → Set H) (B : H → H) (J : ℝ → H → H) (m L lam : ℝ)
    (hm : 0 < m) (hAs : IsStronglyMonotoneOp m A)
    (hJ : IsResolventFamily A J)
    (hBm : IsMonotoneFun B)
    (hL : 0 < L) (hBL : IsLipschitzOp L B)
    (hlam0 : 0 < lam) (hlam1 : lam < 1 / (2 * L))
    (x : ℕ → H) (hrun : FRBSplitting.Weak.IsFRBRun J B (fun _ => lam) x)
    (xs : H) (hxs : xs ∈ FRBSplitting.Weak.zeroSet A B) :
    ∀ k : ℕ, (1 + 2 * m * lam) * ‖x (k + 2) - xs‖ ^ 2
        + 2 * lam * ⟪B (x (k + 2)) - B (x (k + 1)), xs - x (k + 2)⟫_ℝ
        + (1 - lam * L) * ‖x (k + 2) - x (k + 1)‖ ^ 2
      ≤ ‖x (k + 1) - xs‖ ^ 2 + 2 * lam * ⟪B (x (k + 1)) - B (x k), xs - x (k + 1)⟫_ℝ
        + 1 / 2 * ‖x (k + 1) - x k‖ ^ 2 := by sorry

end FRBSplitting.Linear
