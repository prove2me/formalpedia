-- Prove2me | Theorems.Thm_CauchyRiemannIndex_translationInvariant_L2_bound
-- name    : CauchyRiemannIndex.translationInvariant_L2_bound
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-14T21:54:32.690169+00:00
-- url     : https://prove2.me/theorems/da1ddb76-ab51-4f2b-9ef2-7dbd9318e142
-- title:
--   $L^2$ bound for translation-invariant Cauchy–Riemann operators with nondegenerate asymptotics
-- statement:
--   Let $S_\infty$ be a continuous $1$-periodic loop of symmetric $2n\times2n$ matrices whose asymptotic operator $-J_0\partial_t-S_\infty(t)$ is nondegenerate. Then there is a constant $C\ge0$ such that
--   $$\|u\|_{L^2(\mathbb R\times S^1)}\le C\,\big\|\partial_s u+J_0\partial_t u+S_\infty(t)u\big\|_{L^2(\mathbb R\times S^1)}$$
--   for every smooth $u:\mathbb R\times S^1\to\mathbb R^{2n}$ that vanishes for large $|s|$.
--
--   This is the case $p=2$ of the zero-order a priori bound in Wendl, Theorem 4.11 (case $k=1$).
--
--   **Formalization Note.** $S^1=\mathbb R/\mathbb Z$; maps on the cylinder are maps of $(s,t)\in\mathbb R\times\mathbb R$ that are $1$-periodic in $t$, and integrals over $\mathbb R\times S^1$ are over the strip $\mathbb R\times[0,1)$ (`cylMeasure`). Test sections are `IsTestSection` (smooth, $1$-periodic in $t$, zero for large $|s|$). The norms are `eLpNorm · 2 cylMeasure` in `ℝ≥0∞`, the operator is `crOp` with $S(s,t)=S_\infty(t)$, and nondegeneracy is `IsNondegenerate` ($\det(1-\Psi(1))\ne0$ for the fundamental solution $\Psi'=J_0S_\infty\Psi$, $\Psi(0)=1$). $C$ is in `ℝ≥0` and does not depend on $u$.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 4, Theorem 4.11, p. 71 (case k = 1)

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

/-- Let `S∞` be a nondegenerate loop of symmetric matrices. There is a constant `C` such that
every test section `u` of the cylinder `ℝ × S¹` satisfies
`‖u‖_{L²(ℝ × S¹)} ≤ C ‖D u‖_{L²(ℝ × S¹)}`, where `D = ∂ₛ + J₀ ∂ₜ + S∞(t)` is the
translation-invariant Cauchy–Riemann operator.

This is the `p = 2` case of the zero-order a priori bound for `D`. -/
theorem translationInvariant_L2_bound (n : ℕ) (Sinf : ℝ → Mat n) (hS : IsSymLoop Sinf)
    (hnd : IsNondegenerate Sinf) :
    ∃ C : ℝ≥0, ∀ u : ℝ × ℝ → Vec n, IsTestSection u →
      eLpNorm u 2 cylMeasure ≤ C * eLpNorm (crOp (fun x : ℝ × ℝ => Sinf x.2) u) 2 cylMeasure := by
  sorry

end CauchyRiemannIndex
