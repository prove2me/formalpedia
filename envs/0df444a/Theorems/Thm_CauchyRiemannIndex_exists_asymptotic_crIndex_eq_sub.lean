-- Prove2me | Theorems.Thm_CauchyRiemannIndex_exists_asymptotic_crIndex_eq_sub
-- name    : CauchyRiemannIndex.exists_asymptotic_crIndex_eq_sub
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-17T14:50:33.428019+00:00
-- url     : https://prove2.me/theorems/d7fa201b-de94-4446-9472-ce00bf439566
-- title:
--   Cauchy–Riemann operators on the cylinder with prescribed asymptotic Conley–Zehnder indices a, b and index a − b
-- statement:
--   Let $n=1$ and $p=2$. For all integers $a,b$ there exist continuous loops $S^\pm$ of symmetric $2\times2$ matrices with nondegenerate asymptotic operators and
--   $$\mu_{CZ}(-J_0\partial_t-S^+)=a,\qquad\mu_{CZ}(-J_0\partial_t-S^-)=b,$$
--   and a continuous coefficient $S:\mathbb{R}\times S^1\to\mathbb{R}^{2\times2}$ with $S(s,\cdot)\to S^\pm$ uniformly as $s\to\pm\infty$, such that the Cauchy–Riemann operator $D_S=\partial_s+J_0\partial_t+S:W^{1,2}\to L^2$ on the cylinder has index
--   $$\operatorname{ind}D_S=a-b.$$
--
--   This provides, for every prescribed pair of asymptotic Conley–Zehnder indices, one operator on the cylinder whose index is known; it is the reference case for the index formula on the cylinder.
--
--   **Formalization Note** The index is `crIndex 2 S`; loops are `IsSymLoop`, nondegeneracy is `IsNondegenerate`, the Conley–Zehnder index is `asymptoticCZIndex`, and the convergence is `IsAsymptoticTo S Splus Sminus` (positive end first), all from the setting module. Existence only: no particular form of $S$ is asserted.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 5, §5.8, pp. 102-103 (cylinder, trivial bundle)

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

/-- Wendl, Lecture 5 (§ 5.8, pp. 102–103), on the cylinder with the trivial line bundle (`n = 1`)
and `p = 2`: for all integers `a` and `b` there is a Cauchy–Riemann operator `D_S` asymptotic to
nondegenerate loops `S±` of symmetric matrices with `μ_CZ(-J₀ ∂ₜ - S⁺) = a`,
`μ_CZ(-J₀ ∂ₜ - S⁻) = b` and `ind D_S = a - b`. -/
theorem exists_asymptotic_crIndex_eq_sub (a b : ℤ) :
    ∃ (S : ℝ × ℝ → Mat 1) (Splus Sminus : ℝ → Mat 1),
      IsSymLoop Splus ∧ IsSymLoop Sminus ∧ IsNondegenerate Splus ∧ IsNondegenerate Sminus ∧
        asymptoticCZIndex Splus = a ∧ asymptoticCZIndex Sminus = b ∧
          IsAsymptoticTo S Splus Sminus ∧ crIndex 2 S = a - b := by
  sorry

end CauchyRiemannIndex
