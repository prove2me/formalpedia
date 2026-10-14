-- Prove2me | Theorems.Thm_CauchyRiemannIndex_isFredholm
-- name    : CauchyRiemannIndex.isFredholm
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-13T21:03:09.986959+00:00
-- url     : https://prove2.me/theorems/1bdb9c49-e5e1-4bab-a6dd-f417cfad2fa2
-- title:
--   Cauchy–Riemann operators on the cylinder with nondegenerate asymptotics are Fredholm
-- statement:
--   Let $1<p<\infty$, let $S^\pm$ be continuous loops of symmetric matrices and let $S:\mathbb{R}\times S^1\to\mathbb{R}^{2n\times2n}$ be continuous with $S(s,\cdot)\to S^\pm$ uniformly as $s\to\pm\infty$; $D_S=\partial_s+J_0\partial_t+S(s,t)$. Assume that the asymptotic operators $A^\pm=-J_0\partial_t-S^\pm(t)$ are nondegenerate. Then $D_S:W^{1,p}(\mathbb{R}\times S^1,\mathbb{R}^{2n})\to L^p(\mathbb{R}\times S^1,\mathbb{R}^{2n})$ is Fredholm.
--
--   **Formalization Note** $p$ is in `ℝ≥0∞` with `Fact (1 ≤ p)`, $1<p$ and $p\ne\infty$. The hypotheses on $S$ are `IsSymLoop S±` and `IsAsymptoticTo S Splus Sminus`. Nondegeneracy is `IsNondegenerate S±`: $\det(\mathrm{Id}-\Psi(1))\ne0$ for the fundamental solution $\Psi$. "Fredholm" is `IsFredholmCR p S`: finite-dimensional kernel, closed range, finite-dimensional cokernel.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 4, Theorem 4.3, p. 69 (case k = 1, cylinder)

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

/-- Wendl, Theorem 4.3 (p. 69), Fredholm property, case `k = 1`, on the cylinder: if `D_S` is
asymptotic to nondegenerate loops `S±` of symmetric matrices and `1 < p < ∞`, then
`D_S : W^{1,p}(ℝ × S¹, ℝ²ⁿ) → L^p(ℝ × S¹, ℝ²ⁿ)` is Fredholm. -/
theorem isFredholm (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p) (hp' : p ≠ ⊤)
    (Splus Sminus : ℝ → Mat n) (hSplus : IsSymLoop Splus) (hSminus : IsSymLoop Sminus)
    (S : ℝ × ℝ → Mat n) (hS : IsAsymptoticTo S Splus Sminus) (hplus : IsNondegenerate Splus) (hminus : IsNondegenerate Sminus) :
    IsFredholmCR p S := by
  sorry

end CauchyRiemannIndex
