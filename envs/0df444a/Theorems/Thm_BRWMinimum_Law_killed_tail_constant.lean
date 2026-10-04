-- Prove2me | Theorems.Thm_BRWMinimum_Law_killed_tail_constant
-- name    : BRWMinimum.Law.killed_tail_constant
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T02:10:54.869142+00:00
-- url     : https://prove2.me/theorems/e5d509a2-44f9-4fd8-843e-5461547287f8
-- title:
--   Proposition 1.2 — limsup_z limsup_n |e^z 𝐏(Mₙ^kill < (3/2) ln n − z) − C₁| = 0 for some C₁ > 0
-- statement:
--   Under the standing assumptions (1.1), non-lattice $\mathcal L$, (1.3), (1.4), there exists a constant $C_1>0$ such that
--   $$\limsup_{z\to\infty}\ \limsup_{n\to\infty}\ \Big|e^z\,\mathbf P\Big(M_n^{\rm kill}<\frac32\ln n-z\Big)-C_1\Big|=0,$$
--   where $M_n^{\rm kill}$ is the minimum at generation $n$ of the branching random walk started at $0$ and killed below $0$.
--
--   This is the first of the three steps of the proof of Theorem 1.1; the constant $C_1$ is unique and enters the final constant $C^*=C_1c_0$.
--
--   **Formalization Note** The iterated limsup of the nonnegative bounded quantities is expressed by the predicate "$C_1$ is a constant of Proposition 1.2" in its equivalent $\varepsilon$–$Z$–$N$ form (see the definition file).
-- source:
--   Aïdékon, Convergence in law of the minimum of a branching random walk, arXiv:1101.1810v6 (Ann. Probab. 41 (2013)), p. 3, Proposition 1.2

import Mathlib
import Definitions.Def_BRWMinimum_Law_PointProcess
import Definitions.Def_BRWMinimum_Law_BRW
import Definitions.Def_BRWMinimum_Law_RandomWalk

open MeasureTheory ProbabilityTheory Filter Topology

namespace BRWMinimum.Law

/-- Proposition 1.2: there is `C₁ > 0` with
`limsup_{z→∞} limsup_{n→∞} |e^z P(M_n^kill < (3/2) ln n − z) − C₁| = 0`. -/
theorem killed_tail_constant {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : List ℕ → Ω → PointConfig} {L : Measure PointConfig} [IsProbabilityMeasure L]
    (hξ : IsBRW P ξ L)
    (h11 : BoundaryCase L) (hNL : NonLattice L) (h13 : SecondMoment L) (h14 : LogMoments L) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ IsKilledTailConst P ξ C₁ := by sorry

end BRWMinimum.Law
