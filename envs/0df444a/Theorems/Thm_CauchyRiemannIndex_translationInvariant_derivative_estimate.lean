-- Prove2me | Theorems.Thm_CauchyRiemannIndex_translationInvariant_derivative_estimate
-- name    : CauchyRiemannIndex.translationInvariant_derivative_estimate
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-13T22:33:09.502652+00:00
-- url     : https://prove2.me/theorems/96fbde4a-54a0-4b66-8796-8c64e455c940
-- title:
--   Uniform $W^{1,p}$ estimate modulo $L^p$ for translation-invariant Cauchy–Riemann operators on the cylinder
-- statement:
--   Let $1<p<\infty$ and let $S_\infty:\mathbb R\to\mathbb R^{2n\times2n}$ be continuous and $1$-periodic. Then there is a constant $c\ge0$ such that
--   $$\|u\|_{W^{1,p}(\mathbb R\times S^1)}\le c\,\big\|\partial_s u+J_0\partial_t u+S_\infty(t)u\big\|_{L^p(\mathbb R\times S^1)}+c\,\|u\|_{L^p(\mathbb R\times S^1)}$$
--   for every smooth $u:\mathbb R\times S^1\to\mathbb R^{2n}$ that vanishes for large $|s|$. The constant does not depend on $u$ or on the size of its support.
--
--   This is the elliptic estimate for the translation-invariant operator on the whole cylinder, with the lower-order term $\|u\|_{L^p}$ on the right. It is one ingredient of the a priori bound in Wendl, Theorem 4.11 (case $k=1$).
--
--   **Formalization Note.** $S^1=\mathbb R/\mathbb Z$; maps on the cylinder are maps of $(s,t)\in\mathbb R\times\mathbb R$ that are $1$-periodic in $t$, and $L^p(\mathbb R\times S^1)$ is $L^p$ of the strip $\mathbb R\times[0,1)$ (`cylMeasure`). Test sections are `IsTestSection` (smooth, $1$-periodic in $t$, zero for large $|s|$). The norm $\|u\|_{W^{1,p}}$ is `w1pNorm p u` $=\|u\|_p+\|\partial_su\|_p+\|\partial_tu\|_p$ in `ℝ≥0∞`, and the operator is `crOp` with $S(s,t)=S_\infty(t)$. $S_\infty$ need not be symmetric or nondegenerate. $p$ is in `ℝ≥0∞` with $1<p$, $p\ne\infty$; $c$ is in `ℝ≥0`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 4, Theorem 4.11, p. 71 (case k = 1)

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

/-- For `1 < p < ∞` and a continuous `1`-periodic loop `S∞` of matrices, the translation-invariant
operator `D = ∂ₛ + J₀ ∂ₜ + S∞(t)` on the cylinder `ℝ × S¹` satisfies
`‖u‖_{W^{1,p}} ≤ c ‖D u‖_{L^p} + c ‖u‖_{L^p}` for every test section `u`, with one constant `c`
(no bound on the support of `u`). -/
theorem translationInvariant_derivative_estimate (n : ℕ) (p : ℝ≥0∞) (hp : 1 < p) (hp' : p ≠ ⊤)
    (Sinf : ℝ → Mat n) (hS : Continuous Sinf) (hper : Function.Periodic Sinf 1) :
    ∃ c : ℝ≥0, ∀ u : ℝ × ℝ → Vec n, IsTestSection u →
      w1pNorm p u ≤ c * eLpNorm (crOp (fun x : ℝ × ℝ => Sinf x.2) u) p cylMeasure +
        c * eLpNorm u p cylMeasure := by
  sorry

end CauchyRiemannIndex
