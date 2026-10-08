-- Prove2me | Theorems.Thm_FirstOrderOpt_Nonconvex_nonconvex_md_bound_v2
-- name    : FirstOrderOpt.Nonconvex.nonconvex_md_bound_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:17:27.35345+00:00
-- url     : https://prove2.me/theorems/851852e1-609a-453b-b327-8449c38f5495
-- title:
--   Theorem 6.5 — complexity of deterministic nonconvex mirror descent (corrected)
-- statement:
--   Let $\Psi=f+h$ on a closed convex $X$ in a real inner-product space, with $h$ convex, $f$ differentiable along $X$ with $L$-Lipschitz gradient $\nabla f$, and $\nu$ a distance generating function on $X$ with prox-function $V$; let $\Psi^*=\inf_X\Psi$ be finite. The mirror-descent method (6.2.18) generates $x_{k+1}\in X$ as the generalized projection (6.2.6) at $x_k$ with gradient $\nabla f(x_k)$ and stepsize $\gamma_k$; $g_{X,k}:=P_X(x_k,\nabla f(x_k),\gamma_k)=\tfrac1{\gamma_k}(x_k-x_{k+1})$ (6.2.20); $R\in\{1,\dots,N\}$ minimizes $\|g_{X,k}\|$ (6.2.19). If $0<\gamma_k\le 2/L$ for all $k\le N$ with strict inequality for at least one $k$, then
--   $$\|g_{X,R}\|^2\le\frac{L\,D_\Psi^2}{\sum_{k=1}^N\big(\gamma_k-\tfrac L2\gamma_k^2\big)},\qquad D_\Psi^2=\frac{\Psi(x_1)-\Psi^*}L\ (6.2.22).$$
--
--   **Formalization Note.** The retired statement had a free $V$, so with $V\equiv 0$ the prox step pinned nothing down and the iterates were arbitrary (disproved). The retired version took $V$ as a free function (with at most nonnegativity and a three-point identity), which admits $V\equiv 0$; the corrected version uses `FirstOrderOpt.Prox.DistanceGeneratingFunction.V`, the prox-function of a distance generating function on $X$ exactly as in §3.2. $\nabla f$ is tied to $f$ (`HasGradientWithinAt` along $X$) and $L$-Lipschitz on $X$, the standing smoothness assumption of §6.2; $h$ convex and $X$ closed convex are the standing assumptions of problem (6.2.1).
-- source:
--   Lan, First-order and Stochastic Optimization Methods for Machine Learning, Springer 2020, p. 330, Theorem 6.5, with (6.2.18)-(6.2.22)

import Mathlib
import Definitions.Def_FirstOrderOpt_Prox_DistanceGeneratingFunction

namespace FirstOrderOpt.Nonconvex

open scoped RealInnerProductSpace
open FirstOrderOpt.Prox

/-- Theorem 6.5 (deterministic nonconvex mirror descent), Lan p. 330. Let `Ψ := f + h` on the
closed convex set `X`, with `h` convex, `f` differentiable along `X` with `L`-Lipschitz gradient
`fGrad`, and `ν` a distance generating function on `X` with prox-function `V = ν.V`. The MD
algorithm (6.2.18) generates `x (k+1)` as the generalized projection (6.2.6) at `x k` with the
exact gradient and stepsize `γ k`; `gX k := P_X(x k, fGrad (x k), γ k) = (1/γ k)(x k - x (k+1))`
(6.2.20); `R ∈ [1, N]` minimizes `‖gX ·‖` (6.2.19). If `0 < γ k ≤ 2/L` for every `k ∈ [1, N]`
with strict inequality for at least one `k`, then
`‖gX R‖² ≤ L·DΨ² / Σ_{k=1}^N (γ k - Lγ k²/2)`, where `DΨ² = (Ψ(x 1) - Ψ*)/L` (6.2.22) and `Ψ*`
is the infimum of `Ψ` over `X` (assumed finite).

Corrected version: `V` is the Bregman distance of a distance generating function (the retired
free `V` let `V ≡ 0`, so the prox step pinned nothing down), `h` is convex, `X` closed convex,
and `fGrad` is the gradient of `f`, Lipschitz as in the chapter's standing assumption. -/
theorem nonconvex_md_bound_v2 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (X : Set E) (hXconv : Convex ℝ X) (hXclosed : IsClosed X)
    (f h : E → ℝ) (hhconv : ConvexOn ℝ X h)
    (ν : DistanceGeneratingFunction X) (L : ℝ) (hL : 0 < L) (fGrad : E → E)
    (hGrad : ∀ x ∈ X, HasGradientWithinAt f (fGrad x) X x)
    (hSmooth : ∀ x ∈ X, ∀ y ∈ X, ‖fGrad x - fGrad y‖ ≤ L * ‖x - y‖)
    (N : ℕ) (hN : 1 ≤ N)
    (x : ℕ → E) (γ : ℕ → ℝ) (gX : ℕ → E)
    (hx : ∀ k, x k ∈ X)
    (hxDef : ∀ k, 1 ≤ k → k ≤ N → ∀ u ∈ X,
      ⟪fGrad (x k), x (k + 1)⟫ + (1 / γ k) * ν.V (x k) (x (k + 1)) + h (x (k + 1)) ≤
        ⟪fGrad (x k), u⟫ + (1 / γ k) * ν.V (x k) u + h u)
    (hgX : ∀ k, 1 ≤ k → k ≤ N → gX k = (1 / γ k) • (x k - x (k + 1)))
    (hγpos : ∀ k, 1 ≤ k → k ≤ N → 0 < γ k) (hγub : ∀ k, 1 ≤ k → k ≤ N → γ k ≤ 2 / L)
    (hγstrict : ∃ k, 1 ≤ k ∧ k ≤ N ∧ γ k < 2 / L)
    (R : ℕ) (hR : 1 ≤ R ∧ R ≤ N) (hRmin : ∀ k, 1 ≤ k → k ≤ N → ‖gX R‖ ≤ ‖gX k‖)
    (ΨStar : ℝ) (hΨStar : IsGLB ((fun x => f x + h x) '' X) ΨStar)
    (DΨ : ℝ) (hDΨ : DΨ = Real.sqrt ((f (x 1) + h (x 1) - ΨStar) / L)) :
    ‖gX R‖ ^ 2 ≤ (L * DΨ ^ 2) / ∑ k ∈ Finset.Icc 1 N, (γ k - L * (γ k) ^ 2 / 2) := by sorry

end FirstOrderOpt.Nonconvex
