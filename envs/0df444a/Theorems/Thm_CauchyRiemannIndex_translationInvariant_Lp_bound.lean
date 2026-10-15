-- Prove2me | Theorems.Thm_CauchyRiemannIndex_translationInvariant_Lp_bound
-- name    : CauchyRiemannIndex.translationInvariant_Lp_bound
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-13T22:33:09.761646+00:00
-- url     : https://prove2.me/theorems/e4cd9a95-370c-4697-95fc-0dcff128fbbc
-- title:
--   $L^p$ bound for translation-invariant Cauchy–Riemann operators with nondegenerate asymptotics, $p\ge2$
-- statement:
--   Let $2\le p<\infty$ and let $S_\infty$ be a continuous loop of symmetric $2n\times2n$ matrices whose asymptotic operator $-J_0\partial_t-S_\infty(t)$ is nondegenerate. Then there is a constant $c\ge0$ such that
--   $$\|u\|_{L^p(\mathbb R\times S^1)}\le c\,\big\|\partial_s u+J_0\partial_t u+S_\infty(t)u\big\|_{L^p(\mathbb R\times S^1)}$$
--   for every smooth $u:\mathbb R\times S^1\to\mathbb R^{2n}$ that vanishes for large $|s|$.
--
--   This is the zero-order part of the a priori bound in Wendl, Theorem 4.11 (case $k=1$), in the range $p\ge2$.
--
--   **Formalization Note.** $S^1=\mathbb R/\mathbb Z$; maps on the cylinder are maps of $(s,t)\in\mathbb R\times\mathbb R$ that are $1$-periodic in $t$, and $L^p(\mathbb R\times S^1)$ is $L^p$ of the strip $\mathbb R\times[0,1)$ (`cylMeasure`). Test sections are `IsTestSection` (smooth, $1$-periodic in $t$, zero for large $|s|$). The operator is `crOp` with $S(s,t)=S_\infty(t)$. Nondegeneracy is `IsNondegenerate` ($\det(1-\Psi(1))\ne0$ for the fundamental solution $\Psi'=J_0S_\infty\Psi$, $\Psi(0)=1$). $p$ is in `ℝ≥0∞` with $2\le p$, $p\ne\infty$; $c$ is in `ℝ≥0` and does not depend on $u$.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 4, Theorem 4.11, p. 71 (case k = 1)

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

/-- For `2 ≤ p < ∞` and a nondegenerate loop `S∞` of symmetric matrices, the translation-invariant
operator `D = ∂ₛ + J₀ ∂ₜ + S∞(t)` on the cylinder `ℝ × S¹` satisfies `‖u‖_{L^p} ≤ c ‖D u‖_{L^p}`
for every test section `u`, with one constant `c`. -/
theorem translationInvariant_Lp_bound (n : ℕ) (p : ℝ≥0∞) (hp : 2 ≤ p) (hp' : p ≠ ⊤)
    (Sinf : ℝ → Mat n) (hS : IsSymLoop Sinf) (hnd : IsNondegenerate Sinf) :
    ∃ c : ℝ≥0, ∀ u : ℝ × ℝ → Vec n, IsTestSection u →
      eLpNorm u p cylMeasure ≤ c * eLpNorm (crOp (fun x : ℝ × ℝ => Sinf x.2) u) p cylMeasure := by
  sorry

end CauchyRiemannIndex
