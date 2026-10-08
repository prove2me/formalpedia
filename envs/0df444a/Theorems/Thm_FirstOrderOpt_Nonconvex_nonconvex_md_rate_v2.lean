-- Prove2me | Theorems.Thm_FirstOrderOpt_Nonconvex_nonconvex_md_rate_v2
-- name    : FirstOrderOpt.Nonconvex.nonconvex_md_rate_v2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-10-06T06:17:39.07898+00:00
-- url     : https://prove2.me/theorems/5b412d58-b60d-4c9f-a4a5-f72e0c2f8b84
-- title:
--   Corollary 6.4 — nonconvex mirror descent with stepsize $1/L$ (corrected)
-- statement:
--   In the setting of Theorem 6.5 — $\Psi=f+h$ on a closed convex $X$, $h$ convex, $\nabla f$ $L$-Lipschitz, $V$ the prox-function of a distance generating function $\nu$ — run the mirror-descent method (6.2.18) with the constant stepsize $\gamma_k=1/L$ for $k=1,\dots,N$. Then, with $g_{X,k}=L(x_k-x_{k+1})$, $R$ minimizing $\|g_{X,k}\|$ and $D_\Psi^2=(\Psi(x_1)-\Psi^*)/L$,
--   $$\|g_{X,R}\|^2\le\frac{2L^2D_\Psi^2}N.$$
--
--   **Formalization Note.** The retired version took $V$ as a free function (with at most nonnegativity and a three-point identity), which admits $V\equiv 0$; the corrected version uses `FirstOrderOpt.Prox.DistanceGeneratingFunction.V`, the prox-function of a distance generating function on $X$ exactly as in §3.2. $\nabla f$ is tied to $f$ (`HasGradientWithinAt` along $X$) and $L$-Lipschitz on $X$, the standing smoothness assumption of §6.2; $h$ convex and $X$ closed convex are the standing assumptions of problem (6.2.1).
-- source:
--   Lan, First-order and Stochastic Optimization Methods for Machine Learning, Springer 2020, p. 331, Corollary 6.4

import Mathlib
import Definitions.Def_FirstOrderOpt_Prox_DistanceGeneratingFunction

namespace FirstOrderOpt.Nonconvex

open scoped RealInnerProductSpace
open FirstOrderOpt.Prox

/-- Corollary 6.4, Lan p. 331: Theorem 6.5 with the constant stepsize `γ k = 1/L`. Let
`Ψ := f + h` on the closed convex `X`, `h` convex, `f` differentiable along `X` with
`L`-Lipschitz gradient `fGrad`, `ν` a distance generating function on `X` with prox-function
`V = ν.V`. If the MD algorithm (6.2.18) is run with `γ k = 1/L` for `k = 1, …, N`, then
`‖gX R‖² ≤ 2L²DΨ²/N`, with `gX`, `R`, `DΨ` as in Theorem 6.5.

Corrected version: `V` is the Bregman distance of a distance generating function (the retired
free `V` let `V ≡ 0`), `h` convex, `X` closed convex, `fGrad` the Lipschitz gradient of `f`. -/
theorem nonconvex_md_rate_v2 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (X : Set E) (hXconv : Convex ℝ X) (hXclosed : IsClosed X)
    (f h : E → ℝ) (hhconv : ConvexOn ℝ X h)
    (ν : DistanceGeneratingFunction X) (L : ℝ) (hL : 0 < L) (fGrad : E → E)
    (hGrad : ∀ x ∈ X, HasGradientWithinAt f (fGrad x) X x)
    (hSmooth : ∀ x ∈ X, ∀ y ∈ X, ‖fGrad x - fGrad y‖ ≤ L * ‖x - y‖)
    (N : ℕ) (hN : 1 ≤ N)
    (x : ℕ → E) (gX : ℕ → E)
    (hx : ∀ k, x k ∈ X)
    (hxDef : ∀ k, 1 ≤ k → k ≤ N → ∀ u ∈ X,
      ⟪fGrad (x k), x (k + 1)⟫ + L * ν.V (x k) (x (k + 1)) + h (x (k + 1)) ≤
        ⟪fGrad (x k), u⟫ + L * ν.V (x k) u + h u)
    (hgX : ∀ k, 1 ≤ k → k ≤ N → gX k = L • (x k - x (k + 1)))
    (R : ℕ) (hR : 1 ≤ R ∧ R ≤ N) (hRmin : ∀ k, 1 ≤ k → k ≤ N → ‖gX R‖ ≤ ‖gX k‖)
    (ΨStar : ℝ) (hΨStar : IsGLB ((fun x => f x + h x) '' X) ΨStar)
    (DΨ : ℝ) (hDΨ : DΨ = Real.sqrt ((f (x 1) + h (x 1) - ΨStar) / L)) :
    ‖gX R‖ ^ 2 ≤ (2 * L ^ 2 * DΨ ^ 2) / (N : ℝ) := by sorry

end FirstOrderOpt.Nonconvex
