-- Prove2me | Theorems.Thm_CauchyRiemannIndex_plane_cauchyRiemann_estimate
-- name    : CauchyRiemannIndex.plane_cauchyRiemann_estimate
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-15T07:18:07.016967+00:00
-- url     : https://prove2.me/theorems/f78db959-f6ac-4cac-9476-7457e78aae94
-- title:
--   The $L^p$ estimate for $\partial_s+J_0\partial_t$ on compactly supported maps $\mathbb R^2\to\mathbb R^{2n}$
-- statement:
--   Let $1<p<\infty$ and $n\in\mathbb N$, and let $J_0=\begin{pmatrix}0&-\mathrm{Id}\\ \mathrm{Id}&0\end{pmatrix}$ be the standard complex structure on $\mathbb R^{2n}$. There is a constant $A$ such that every continuously differentiable map $v:\mathbb R^2\to\mathbb R^{2n}$ with compact support satisfies
--   $$\|\partial_s v\|_{L^p(\mathbb R^2)}+\|\partial_t v\|_{L^p(\mathbb R^2)}\le A\,\|\partial_s v+J_0\,\partial_t v\|_{L^p(\mathbb R^2)},$$
--   where $(s,t)$ are the coordinates of $\mathbb R^2$ and the measure is Lebesgue measure.
--
--   This is the basic $L^p$ elliptic estimate for the Cauchy–Riemann operator $\partial_s+J_0\partial_t$ in real notation, in the form used for linear Cauchy–Riemann type operators on Riemann surfaces and cylinders (Wendl, Lecture 4).
--
--   **Formalization Note.** $\mathbb R^{2n}$ is `EuclideanSpace ℝ (Fin n ⊕ Fin n)`, $J_0$ is `Matrix.J`, acting through `Matrix.toEuclideanLin`. Points of the plane are pairs $(s,t)\in\mathbb R\times\mathbb R$; $\partial_s v$ and $\partial_t v$ are `partialS v x = fderiv ℝ v x (1, 0)` and `partialT v x = fderiv ℝ v x (0, 1)`. $C^1$ means `ContDiff ℝ 1`. Norms are `eLpNorm` with values in $[0,\infty]$, for an exponent `p : ℝ≥0∞` with $1<p$ and $p\ne\infty$. The constant $A$ is chosen before $v$; the measure on $\mathbb R\times\mathbb R$ is `volume`.
-- source:
--   E. M. Stein, Singular Integrals and Differentiability Properties of Functions, Princeton 1970, Chapter III, § 1.3, Proposition 4 (p. 60), written for maps into R^{2n} = C^n with the standard complex structure J_0

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace CauchyRiemannIndex

open MeasureTheory Matrix
open scoped ENNReal NNReal

/-- For `1 < p < ∞` there is `A` such that every `C¹` map `v : ℝ × ℝ → ℝ²ⁿ` with compact support
satisfies `‖∂ₛv‖_p + ‖∂ₜv‖_p ≤ A ‖∂ₛv + J₀ ∂ₜv‖_p` on the plane. -/
theorem plane_cauchyRiemann_estimate (n : ℕ) (p : ℝ≥0∞) (hp : 1 < p) (hp' : p ≠ ⊤) :
    ∃ A : ℝ≥0, ∀ v : ℝ × ℝ → Vec n, ContDiff ℝ 1 v → HasCompactSupport v →
      eLpNorm (partialS v) p volume + eLpNorm (partialT v) p volume ≤
        A * eLpNorm (fun x => partialS v x + Matrix.toEuclideanLin (J₀ n) (partialT v x)) p volume := by
  sorry

end CauchyRiemannIndex
