-- Prove2me | Theorems.Thm_CauchyRiemannIndex_translationInvariant_slab_L2_bound
-- name    : CauchyRiemannIndex.translationInvariant_slab_L2_bound
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-14T20:51:17.404981+00:00
-- url     : https://prove2.me/theorems/d87d56df-eca7-4986-b150-460d81a4160f
-- title:
--   Slab-wise $L^2$ amalgam bound for translation-invariant Cauchy–Riemann operators with nondegenerate asymptotics, $p\ge2$
-- statement:
--   Let $2\le p<\infty$ and let $S_\infty$ be a continuous $1$-periodic loop of symmetric $2n\times2n$ matrices whose asymptotic operator $-J_0\partial_t-S_\infty(t)$ is nondegenerate. Write $D=\partial_s+J_0\partial_t+S_\infty(t)$ for the translation-invariant Cauchy–Riemann operator on the cylinder $\mathbb R\times S^1$. Then there is a constant $K\ge0$ such that
--   $$\int_{\mathbb R}\Big(\int_{[s,s+1]\times S^1}|u|^2\Big)^{p/2}ds\;\le\;K\int_{\mathbb R\times S^1}|Du|^p$$
--   for every smooth $u:\mathbb R\times S^1\to\mathbb R^{2n}$ that vanishes for large $|s|$.
--
--   The left side is the $p$-th power of the $\ell^p(L^2)$ amalgam norm of $u$ over unit slabs of the cylinder. The statement is a zero-order a priori bound for $D$ (Wendl, Theorem 4.11, case $k=1$), in a form that is weaker than the $L^p$ norm for $p>2$; it is used for the bound $\|u\|_{L^p}\le c\|Du\|_{L^p}$.
--
--   **Formalization Note.** $S^1=\mathbb R/\mathbb Z$; maps on the cylinder are maps of $(s,t)\in\mathbb R^2$ that are $1$-periodic in $t$, integrals over $\mathbb R\times S^1$ are over the strip $\mathbb R\times[0,1)$ (`cylMeasure`), and the slab $[s,s+1]\times S^1$ is `Set.Icc s (s + 1) ×ˢ Set.Ico 0 1` with Lebesgue measure. All integrals are lower Lebesgue integrals of `‖·‖ₑ` powers, so no integrability is assumed. Test sections are `IsTestSection` (smooth, $1$-periodic in $t$, zero for large $|s|$); the operator is `crOp` with $S(s,t)=S_\infty(t)$. The loop is `IsSymLoop`; nondegeneracy is `IsNondegenerate` ($\det(1-\Psi(1))\ne0$ for the fundamental solution $\Psi'=J_0S_\infty\Psi$, $\Psi(0)=1$). $p$ is a real number with $2\le p$; $K\in\mathbb R_{\ge0}$ does not depend on $u$.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 4, Theorem 4.11, p. 71 (setting of the translation-invariant operator, case k = 1)

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

/-- Let `2 ≤ p < ∞` and let `S∞` be a nondegenerate loop of symmetric matrices. There is a
constant `K` such that every test section `u` of the cylinder `ℝ × S¹` satisfies
`∫_ℝ (∫_{[s, s+1] × [0,1)} |u|²)^{p/2} ds ≤ K ∫_{ℝ × [0,1)} |D u|^p`,
where `D = ∂ₛ + J₀ ∂ₜ + S∞(t)` is the translation-invariant Cauchy–Riemann operator.

The left side is the `p/2`-th power amalgam norm of `u` over the unit slabs of the cylinder. -/
theorem translationInvariant_slab_L2_bound (n : ℕ) (p : ℝ) (hp : 2 ≤ p)
    (Sinf : ℝ → Mat n) (hS : IsSymLoop Sinf) (hnd : IsNondegenerate Sinf) :
    ∃ K : ℝ≥0, ∀ u : ℝ × ℝ → Vec n, IsTestSection u →
      (∫⁻ s : ℝ, (∫⁻ x in Set.Icc s (s + 1) ×ˢ Set.Ico (0 : ℝ) 1, ‖u x‖ₑ ^ (2 : ℝ)) ^ (p / 2)) ≤
        K * ∫⁻ x, ‖crOp (fun x : ℝ × ℝ => Sinf x.2) u x‖ₑ ^ p ∂cylMeasure := by
  sorry

end CauchyRiemannIndex
