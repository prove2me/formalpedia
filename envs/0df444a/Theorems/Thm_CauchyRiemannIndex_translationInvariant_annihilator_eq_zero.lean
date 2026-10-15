-- Prove2me | Theorems.Thm_CauchyRiemannIndex_translationInvariant_annihilator_eq_zero
-- name    : CauchyRiemannIndex.translationInvariant_annihilator_eq_zero
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-13T23:12:51.902177+00:00
-- url     : https://prove2.me/theorems/65c4af56-85a7-45a1-9fa4-b6ede0deb9a9
-- title:
--   For $1<q<2$, an $L^q$ map orthogonal to the image of a nondegenerate translation-invariant Cauchy–Riemann operator on test sections vanishes
-- statement:
--   Let $1<q<2$ and let $S_\infty$ be a continuous loop of symmetric $2n\times2n$ matrices whose asymptotic operator $-J_0\partial_t-S_\infty(t)$ is nondegenerate. If $g\in L^q(\mathbb R\times S^1,\mathbb R^{2n})$ satisfies
--   $$\int_{\mathbb R\times S^1}\big\langle \partial_s u+J_0\partial_t u+S_\infty(t)u,\ g\big\rangle=0$$
--   for every smooth $u:\mathbb R\times S^1\to\mathbb R^{2n}$ that vanishes for large $|s|$, then $g=0$.
--
--   This is the uniqueness of $L^q$ weak solutions of the formal adjoint equation $-\partial_s g+J_0\partial_t g+S_\infty(t)g=0$ for $1<q<2$. It is the dual-exponent counterpart of the density of the range of $\partial_s+J_0\partial_t+S_\infty(t)$ on test sections in $L^p$ for $p>2$ (Wendl, Theorem 4.11, case $k=1$).
--
--   **Formalization Note.** $S^1=\mathbb R/\mathbb Z$; maps on the cylinder are maps of $(s,t)\in\mathbb R\times\mathbb R$ that are $1$-periodic in $t$, and $L^q(\mathbb R\times S^1)$ is `LpCyl n q`, i.e. $L^q$ of the strip $\mathbb R\times[0,1)$ (`cylMeasure`). Test sections are `IsTestSection` (smooth, $1$-periodic in $t$, zero for large $|s|$). The operator is `crOp` with $S(s,t)=S_\infty(t)$. Nondegeneracy is `IsNondegenerate` ($\det(1-\Psi(1))\ne0$ for the fundamental solution $\Psi'=J_0S_\infty\Psi$, $\Psi(0)=1$). $q$ is in `ℝ≥0∞` with `Fact (1 ≤ q)`, $1<q$ and $q<2$.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 4, Theorem 4.11, p. 71 (case k = 1)

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

/-- For `1 < q < 2` and a nondegenerate loop `S∞` of symmetric matrices, an `L^q` map `g` on the
cylinder `ℝ × S¹` with `∫ ⟨D u, g⟩ = 0` for every test section `u`, where
`D = ∂ₛ + J₀ ∂ₜ + S∞(t)`, is zero. -/
theorem translationInvariant_annihilator_eq_zero (n : ℕ) (q : ℝ≥0∞) [Fact (1 ≤ q)] (hq : 1 < q)
    (hq2 : q < 2) (Sinf : ℝ → Mat n) (hS : IsSymLoop Sinf) (hnd : IsNondegenerate Sinf)
    (g : LpCyl n q)
    (hg : ∀ u : ℝ × ℝ → Vec n, IsTestSection u →
      ∫ x, inner ℝ (crOp (fun x : ℝ × ℝ => Sinf x.2) u x) (g x) ∂cylMeasure = 0) :
    g = 0 := by
  sorry

end CauchyRiemannIndex
