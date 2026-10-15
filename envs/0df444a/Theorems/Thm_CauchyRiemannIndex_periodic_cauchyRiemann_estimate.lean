-- Prove2me | Theorems.Thm_CauchyRiemannIndex_periodic_cauchyRiemann_estimate
-- name    : CauchyRiemannIndex.periodic_cauchyRiemann_estimate
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-15T07:18:07.028731+00:00
-- url     : https://prove2.me/theorems/c6f23952-002e-4e98-bdba-bd8cea6826ca
-- title:
--   The $L^p$ estimate for $\partial_s+J_0\partial_t$ on the cylinder $\mathbb R\times S^1$, up to a lower-order term
-- statement:
--   Let $1<p<\infty$ and $n\in\mathbb N$, and let $J_0=\begin{pmatrix}0&-\mathrm{Id}\\ \mathrm{Id}&0\end{pmatrix}$. There is a constant $A$ such that every continuously differentiable map $u:\mathbb R\times\mathbb R\to\mathbb R^{2n}$ which is $1$-periodic in the second variable, $u(s,t+1)=u(s,t)$, and vanishes for $|s|$ large satisfies
--   $$\|\partial_s u\|_{L^p}+\|\partial_t u\|_{L^p}\le A\,\|\partial_s u+J_0\,\partial_t u\|_{L^p}+A\,\|u\|_{L^p},$$
--   where all norms are taken over the cylinder $\mathbb R\times S^1$, i.e. over the strip $\mathbb R\times[0,1)$ with Lebesgue measure.
--
--   It is the $L^p$ estimate for the standard Cauchy–Riemann operator on the cylinder, the case $S=0$ of the local estimate for Cauchy–Riemann type operators $\partial_s+J_0\partial_t+S$ (Wendl, Proposition 4.8). The constant does not depend on the size of the support of $u$.
--
--   **Formalization Note.** $\mathbb R^{2n}$ is `EuclideanSpace ℝ (Fin n ⊕ Fin n)`, $J_0$ is `Matrix.J`, acting through `Matrix.toEuclideanLin`. Points of the plane are pairs $(s,t)\in\mathbb R\times\mathbb R$; $\partial_s v$ and $\partial_t v$ are `partialS v x = fderiv ℝ v x (1, 0)` and `partialT v x = fderiv ℝ v x (0, 1)`. $C^1$ means `ContDiff ℝ 1`. Norms are `eLpNorm` with values in $[0,\infty]$, for an exponent `p : ℝ≥0∞` with $1<p$ and $p\ne\infty$. Lebesgue measure on the strip is `cylMeasure`. Vanishing for large $|s|$ means: there is $R$ with $u(s,t)=0$ whenever $R<|s|$. The constant $A$ is chosen before $u$ (and before $R$).
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 4, Proposition 4.8, p. 71 (local estimate for Cauchy–Riemann type operators)

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace CauchyRiemannIndex

open MeasureTheory Matrix
open scoped ENNReal NNReal

/-- For `1 < p < ∞` there is `A` such that every `C¹` map `u : ℝ × ℝ → ℝ²ⁿ` that is `1`-periodic
in `t` and vanishes for large `|s|` satisfies, on the cylinder `ℝ × S¹`,
`‖∂ₛu‖_p + ‖∂ₜu‖_p ≤ A ‖∂ₛu + J₀ ∂ₜu‖_p + A ‖u‖_p`. -/
theorem periodic_cauchyRiemann_estimate (n : ℕ) (p : ℝ≥0∞) (hp : 1 < p) (hp' : p ≠ ⊤) :
    ∃ A : ℝ≥0, ∀ u : ℝ × ℝ → Vec n, ContDiff ℝ 1 u → (∀ s t, u (s, t + 1) = u (s, t)) →
      (∃ R : ℝ, ∀ s t, R < |s| → u (s, t) = 0) →
      eLpNorm (partialS u) p cylMeasure + eLpNorm (partialT u) p cylMeasure ≤
        A * eLpNorm (fun x => partialS u x + Matrix.toEuclideanLin (J₀ n) (partialT u x)) p
            cylMeasure + A * eLpNorm u p cylMeasure := by
  sorry

end CauchyRiemannIndex
