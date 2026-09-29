-- Prove2me | Theorems.Thm_FirstOrderOpt_Nonconvex_nonconvex_md_rate
-- name    : FirstOrderOpt.Nonconvex.nonconvex_md_rate
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-19T21:03:51.536983+00:00
-- url     : https://prove2.me/theorems/afce0c03-4141-4a35-ae72-14169956b3f0
-- title:
--   Corollary 6.4 — constant-stepsize instantiation of Theorem 6.5
-- statement:
--   Specializing `nonconvex_md_bound` (Theorem 6.5) to the constant stepsize $\gamma_k = 1/L$ for
--   every $k=1,\dots,N$:
--
--   **Corollary 6.4.**
--   $$\|g_{X,R}\|^2 \le \frac{2L^2 D_\Psi^2}{N}.$$
--
--   This is the clean, explicit-constant headline rate for the deterministic nonconvex MD
--   algorithm: $O(1/N)$ in the squared generalized-projected-gradient norm, i.e. $O(1/\varepsilon)$
--   iterations to reach $\|g_{X,R}\|\le\sqrt\varepsilon$ — the standard nonconvex first-order
--   complexity, here obtained via the same generalized-projection apparatus used for the
--   constrained composite problem rather than the unconstrained, smooth-only setting most
--   textbook treatments give this rate for.
--
--   **Formalization Note.** Restates the generation rule (6.2.18) with $\gamma_k=1/L$ substituted
--   directly (the $\tfrac1{\gamma_k}=L$ coefficient appears explicitly in the minimality
--   hypothesis), matching how `nonconvex_md_bound`'s general bound needs the concrete schedule
--   plugged in to reach the clean $2L^2D_\Psi^2/N$ form — the same "instantiate, don't just cite,
--   the general theorem" approach used for the goal theorem of chunk `03-deterministic`.
-- source:
--   Lan, First-order and Stochastic Optimization Methods for Machine Learning, Springer 2020, p. 331, Corollary 6.4

import Mathlib

namespace FirstOrderOpt.Nonconvex

open scoped RealInnerProductSpace

/-- Corollary 6.4. Specializing `nonconvex_md_bound` (Theorem 6.5) to the constant stepsize `γ k =
1/L` for every `k = 1,…,N` gives `‖gX R‖² ≤ 2L²DΨ²/N`. -/
theorem nonconvex_md_rate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (X : Set E) (f h : E → ℝ) (V : E → E → ℝ) (L : ℝ) (hL : 0 < L) (fGrad : E → E)
    (hSmooth : ∀ x ∈ X, ∀ y ∈ X, f y - f x - ⟪fGrad x, y - x⟫ ≤ (L / 2) * ‖y - x‖ ^ 2)
    (N : ℕ) (hN : 1 ≤ N)
    (x : ℕ → E) (gX : ℕ → E)
    (hx : ∀ k, x k ∈ X)
    (hxDef : ∀ k, 1 ≤ k → k ≤ N → ∀ u ∈ X,
      ⟪fGrad (x k), x (k + 1)⟫ + L * V (x k) (x (k + 1)) + h (x (k + 1)) ≤
        ⟪fGrad (x k), u⟫ + L * V (x k) u + h u)
    (hgX : ∀ k, 1 ≤ k → k ≤ N → gX k = L • (x k - x (k + 1)))
    (R : ℕ) (hR : 1 ≤ R ∧ R ≤ N) (hRmin : ∀ k, 1 ≤ k → k ≤ N → ‖gX R‖ ≤ ‖gX k‖)
    (ΨStar : ℝ) (hΨStar : IsGLB ((fun x => f x + h x) '' X) ΨStar)
    (DΨ : ℝ) (hDΨ : DΨ = Real.sqrt ((f (x 1) + h (x 1) - ΨStar) / L)) :
    ‖gX R‖ ^ 2 ≤ (2 * L ^ 2 * DΨ ^ 2) / (N : ℝ) := by sorry

end FirstOrderOpt.Nonconvex
