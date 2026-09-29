-- Prove2me | Theorems.Thm_FirstOrderOpt_Nonconvex_nonconvex_md_bound
-- name    : FirstOrderOpt.Nonconvex.nonconvex_md_bound
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-19T21:03:25.536465+00:00
-- url     : https://prove2.me/theorems/dad15ef1-89f5-40bd-be80-0fe95aac6f15
-- title:
--   Theorem 6.5 — deterministic nonconvex mirror descent complexity
-- statement:
--   The (deterministic) **nonconvex mirror descent (MD) algorithm**: from $x_1\in X$, for
--   $k=1,\dots,N$ compute $x_{k+1} = \arg\min_{u\in X}\{\langle\nabla f(x_k),u\rangle + \tfrac1{
--   \gamma_k}V(x_k,u) + h(u)\}$ (Eq. (6.2.18)), $g_{X,k} := P_X(x_k,\nabla f(x_k),\gamma_k)$ (Eq.
--   (6.2.20)); output $x_R$ where $R := \arg\min_{k\in\{1,\dots,N\}}\|g_{X,k}\|$ (Eq. (6.2.19)).
--   Assume $f\in C^{1,1}_L(X)$ ($L$-Lipschitz gradient).
--
--   **Theorem 6.5.** If $0<\gamma_k\le 2/L$ for every $k$, with $\gamma_k<2/L$ for at least one
--   $k$, then
--   $$\|g_{X,R}\|^2 \le \frac{L D_\Psi^2}{\sum_{k=1}^N(\gamma_k - L\gamma_k^2/2)}, \qquad D_\Psi :=
--   \Big(\frac{\Psi(x_1)-\Psi^*}{L}\Big)^{1/2}.$$
--
--   This is the deterministic ancestor of the mission's goal theorem, and provides the basis for
--   the stochastic RSMD algorithm's convergence analysis: it establishes that driving
--   $\|g_{X,\cdot}\|$ to zero drives the composite objective to a stationary point (Lemma 6.3,
--   not itself a milestone here), and pins down the exact non-asymptotic rate at which a
--   generalized-projected-gradient method achieves this for a smooth-but-possibly-nonconvex $f$
--   plus a simple nonsmooth $h$.
--
--   **Formalization Note.** $D_\Psi^2 := (\Psi(x_1)-\Psi^*)/L$ depends on the objective gap *at
--   initialization* $x_1$, never at a later iterate — kept as its own named hypothesis-defined
--   quantity (`hDΨ`), not derived, per the chapter-specific pitfall this brief flags. $\Psi^*$ is
--   the greatest lower bound of $\Psi:=f+h$ over $X$ (`IsGLB`), matching "$\Psi$ is bounded below
--   over $X$" (Eq. (6.2.1)'s standing assumption). $R$'s defining property (6.2.19) is the
--   hypothesis that `‖gX R‖ ≤ ‖gX k‖` for every `k ∈ [1,N]`, i.e. `R` genuinely minimizes the
--   norm, rather than an `argmin` term.
-- source:
--   Lan, First-order and Stochastic Optimization Methods for Machine Learning, Springer 2020, p. 330, Theorem 6.5

import Mathlib

namespace FirstOrderOpt.Nonconvex

open scoped RealInnerProductSpace

/-- Theorem 6.5 (deterministic nonconvex mirror descent complexity). `Ψ := f + h` on the closed
convex `X`, `f` has `L`-Lipschitz gradient `fGrad`. The MD algorithm (6.2.18) generates `x` with
`x (k+1)` the generalized projection at `x k` using the exact gradient `fGrad (x k)`; `gX k :=
P_X(x k, fGrad (x k), γ k)` (6.2.20). `R` is chosen (6.2.19) to minimize `‖gX ·‖` over `1,…,N`. If
`0 < γ k ≤ 2/L` for every `k ∈ [1,N]` with strict inequality for at least one `k`, then
`‖gX R‖² ≤ L·DΨ² / Σ_{k=1}^N (γ k - Lγ k²/2)`, where `DΨ² = (Ψ(x 1) - Ψ*)/L` (6.2.22). -/
theorem nonconvex_md_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (X : Set E) (f h : E → ℝ) (V : E → E → ℝ) (L : ℝ) (hL : 0 < L) (fGrad : E → E)
    (hSmooth : ∀ x ∈ X, ∀ y ∈ X, f y - f x - ⟪fGrad x, y - x⟫ ≤ (L / 2) * ‖y - x‖ ^ 2)
    (N : ℕ) (hN : 1 ≤ N)
    (x : ℕ → E) (γ : ℕ → ℝ) (gX : ℕ → E)
    (hx : ∀ k, x k ∈ X)
    (hxDef : ∀ k, 1 ≤ k → k ≤ N → ∀ u ∈ X,
      ⟪fGrad (x k), x (k + 1)⟫ + (1 / γ k) * V (x k) (x (k + 1)) + h (x (k + 1)) ≤
        ⟪fGrad (x k), u⟫ + (1 / γ k) * V (x k) u + h u)
    (hgX : ∀ k, 1 ≤ k → k ≤ N → gX k = (1 / γ k) • (x k - x (k + 1)))
    (hγpos : ∀ k, 1 ≤ k → k ≤ N → 0 < γ k) (hγub : ∀ k, 1 ≤ k → k ≤ N → γ k ≤ 2 / L)
    (hγstrict : ∃ k, 1 ≤ k ∧ k ≤ N ∧ γ k < 2 / L)
    (R : ℕ) (hR : 1 ≤ R ∧ R ≤ N) (hRmin : ∀ k, 1 ≤ k → k ≤ N → ‖gX R‖ ≤ ‖gX k‖)
    (ΨStar : ℝ) (hΨStar : IsGLB ((fun x => f x + h x) '' X) ΨStar)
    (DΨ : ℝ) (hDΨ : DΨ = Real.sqrt ((f (x 1) + h (x 1) - ΨStar) / L)) :
    ‖gX R‖ ^ 2 ≤ (L * DΨ ^ 2) / ∑ k ∈ Finset.Icc 1 N, (γ k - L * (γ k) ^ 2 / 2) := by sorry

end FirstOrderOpt.Nonconvex
