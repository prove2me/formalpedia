-- Prove2me | Theorems.Thm_BRWMinimum_Law_minimum_tail_upper_bound
-- name    : BRWMinimum.Law.minimum_tail_upper_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T01:36:14.306977+00:00
-- url     : https://prove2.me/theorems/482705ab-534c-498f-a26b-e8452b49f9d1
-- title:
--   Corollary 3.5 — 𝐏(Mₙ ≤ (3/2) ln n − y) ≤ (1 + c₁₀(1 + y)) e^{−y}
-- statement:
--   Let $M_n$ be the minimum at generation $n$ of a branching random walk started at $0$ satisfying the standing assumptions (boundary case (1.1), non-lattice $\mathcal L$, (1.3) and (1.4)), and let $a_n(y)=\frac32\ln n-y$. There is a constant $c_{10}>0$ such that for every $y\ge0$ and every integer $n\ge1$,
--   $$\mathbf P\big(M_n\le a_n(y)\big)\le\big(1+c_{10}(1+y)\big)e^{-y}.$$
--
--   This is the a priori upper bound on the lower tail of the minimum around $\frac32\ln n$; in the proof of Theorem 1.1 it controls the particles of $\mathcal Z[A]$ that sit far above level $A$.
--
--   **Formalization Note** $c_{10}$ is the constant of Corollary 3.4 in the paper; this statement asserts the existence of such a constant without stating Corollary 3.4 itself. $M_n$ is an extended real, $+\infty$ on extinction, so extinction does not contribute to the event.
-- source:
--   Aïdékon, Convergence in law of the minimum of a branching random walk, arXiv:1101.1810v6 (Ann. Probab. 41 (2013)), p. 16, Corollary 3.5

import Mathlib
import Definitions.Def_BRWMinimum_Law_PointProcess
import Definitions.Def_BRWMinimum_Law_BRW
import Definitions.Def_BRWMinimum_Law_RandomWalk

open MeasureTheory ProbabilityTheory Filter Topology

namespace BRWMinimum.Law

/-- Corollary 3.5: `P(M_n ≤ a_n(y)) ≤ (1 + c₁₀(1 + y)) e^{−y}` for `y ≥ 0`, `n ≥ 1`. -/
theorem minimum_tail_upper_bound {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : List ℕ → Ω → PointConfig} {L : Measure PointConfig} [IsProbabilityMeasure L]
    (hξ : IsBRW P ξ L)
    (h11 : BoundaryCase L) (hNL : NonLattice L) (h13 : SecondMoment L) (h14 : LogMoments L) :
    ∃ c : ℝ, 0 < c ∧ ∀ y : ℝ, 0 ≤ y → ∀ n : ℕ, 1 ≤ n →
      P {ω | minPos ξ 0 n ω ≤ (((3 / 2 : ℝ) * Real.log n - y : ℝ) : EReal)} ≤
        ENNReal.ofReal ((1 + c * (1 + y)) * Real.exp (-y)) := by sorry

end BRWMinimum.Law
