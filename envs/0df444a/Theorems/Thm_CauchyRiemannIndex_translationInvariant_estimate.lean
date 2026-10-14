-- Prove2me | Theorems.Thm_CauchyRiemannIndex_translationInvariant_estimate
-- name    : CauchyRiemannIndex.translationInvariant_estimate
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-13T21:53:12.964612+00:00
-- url     : https://prove2.me/theorems/f8bf33ce-4109-4a01-b876-2dfb5f980de3
-- title:
--   A priori $W^{1,p}$ bound for translation-invariant Cauchy–Riemann operators with nondegenerate asymptotics on the cylinder
-- statement:
--   Let $1<p<\infty$ and let $S_\infty$ be a continuous loop of symmetric $2n\times2n$ matrices whose asymptotic operator $-J_0\partial_t-S_\infty(t)$ is nondegenerate. Then there is a constant $c\ge0$ such that
--   $$\|u\|_{W^{1,p}(\mathbb R\times S^1)}\le c\,\big\|\partial_s u+J_0\partial_t u+S_\infty(t)u\big\|_{L^p(\mathbb R\times S^1)}$$
--   for every smooth $u:\mathbb R\times S^1\to\mathbb R^{2n}$ that vanishes for large $|s|$.
--
--   This is the quantitative half of the statement that the translation-invariant operator $\partial_s+J_0\partial_t+S_\infty(t):W^{1,p}\to L^p$ is an isomorphism (Wendl, Theorem 4.11, case $k=1$), and the bound used near the cylindrical ends of general asymptotically translation-invariant operators.
--
--   **Formalization Note.** $S^1=\mathbb R/\mathbb Z$; maps on the cylinder are maps of $(s,t)\in\mathbb R\times\mathbb R$ that are $1$-periodic in $t$, and $L^p(\mathbb R\times S^1)$ is $L^p$ of the strip $\mathbb R\times[0,1)$ (`cylMeasure`). Test sections are `IsTestSection` (smooth, $1$-periodic in $t$, zero for large $|s|$). The norm $\|u\|_{W^{1,p}}$ is `w1pNorm p u` $=\|u\|_p+\|\partial_su\|_p+\|\partial_tu\|_p$ in `ℝ≥0∞`, and the operator is `crOp` with $S(s,t)=S_\infty(t)$. Nondegeneracy is `IsNondegenerate` ($\det(1-\Psi(1))\ne0$ for the fundamental solution $\Psi'=J_0S_\infty\Psi$, $\Psi(0)=1$). $p$ is in `ℝ≥0∞` with `Fact (1 ≤ p)`, $1<p$, $p\ne\infty$; $c$ is in `ℝ≥0` and does not depend on $u$.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 4, Theorem 4.11, p. 71 (case k = 1)

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

/-- For `1 < p < ∞` and a nondegenerate loop `S∞` of symmetric matrices, the
translation-invariant operator `D = ∂ₛ + J₀ ∂ₜ + S∞(t)` on the cylinder `ℝ × S¹` satisfies
`‖u‖_{W^{1,p}} ≤ c ‖D u‖_{L^p}` for every test section `u`, with one constant `c`. -/
theorem translationInvariant_estimate (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p)
    (hp' : p ≠ ⊤) (Sinf : ℝ → Mat n) (hS : IsSymLoop Sinf) (hnd : IsNondegenerate Sinf) :
    ∃ c : ℝ≥0, ∀ u : ℝ × ℝ → Vec n, IsTestSection u →
      w1pNorm p u ≤ c * eLpNorm (crOp (fun x : ℝ × ℝ => Sinf x.2) u) p cylMeasure := by
  sorry

end CauchyRiemannIndex
