-- Prove2me | Theorems.Thm_BRWMinimum_Law_killed_tail_uniform
-- name    : BRWMinimum.Law.killed_tail_uniform
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T01:53:29.689991+00:00
-- url     : https://prove2.me/theorems/2403ddd3-1ce6-4e73-a9f5-1d158a88ff31
-- title:
--   Corollary 3.2 — |e^z 𝐏(Mₙ^kill < (3/2) ln n − z) − C₁| ≤ ε uniformly for z ∈ [A, (3/2) ln n − A], n ≥ N
-- statement:
--   Let $M_n^{\rm kill}$ be the minimum at generation $n$ of the branching random walk (started at $0$) killed below $0$, under the standing assumptions (1.1), non-lattice $\mathcal L$, (1.3), (1.4). There is a constant $C_1>0$ such that for every $\varepsilon>0$ there exist a real $A\ge0$ and an integer $N\ge1$ such that for every $n\ge N$ and every $z\in[A,\frac32\ln n-A]$,
--   $$\Big|e^z\,\mathbf P\Big(M_n^{\rm kill}<\frac32\ln n-z\Big)-C_1\Big|\le\varepsilon.$$
--
--   So the lower tail of the killed minimum is $C_1e^{-z}$, uniformly in a window of $z$ that grows with $n$. Proposition 1.2 follows immediately.
--
--   **Formalization Note** In the paper $C_1:=C_2/(1-e^{-1})$ with $C_2$ the constant of Proposition 3.1; Proposition 3.1 is not part of this mission, so the statement asserts the existence of $C_1>0$. The estimate is uniform in $z$ over the window, not "for each $z$, eventually in $n$". $M_n^{\rm kill}=+\infty$ when the killed process has died out.
-- source:
--   Aïdékon, Convergence in law of the minimum of a branching random walk, arXiv:1101.1810v6 (Ann. Probab. 41 (2013)), p. 12, Corollary 3.2

import Mathlib
import Definitions.Def_BRWMinimum_Law_PointProcess
import Definitions.Def_BRWMinimum_Law_BRW
import Definitions.Def_BRWMinimum_Law_RandomWalk

open MeasureTheory ProbabilityTheory Filter Topology

namespace BRWMinimum.Law

/-- Corollary 3.2: uniform tail of the killed minimum on the window `[A, (3/2) ln n − A]`. -/
theorem killed_tail_uniform {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : List ℕ → Ω → PointConfig} {L : Measure PointConfig} [IsProbabilityMeasure L]
    (hξ : IsBRW P ξ L)
    (h11 : BoundaryCase L) (hNL : NonLattice L) (h13 : SecondMoment L) (h14 : LogMoments L) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, 0 ≤ A ∧ ∃ N : ℕ, 1 ≤ N ∧
      ∀ n : ℕ, N ≤ n → ∀ z ∈ Set.Icc A ((3 / 2 : ℝ) * Real.log n - A),
        |Real.exp z * (P {ω | minPosKilled ξ 0 n ω <
            (((3 / 2 : ℝ) * Real.log n - z : ℝ) : EReal)}).toReal - C₁| ≤ ε := by sorry

end BRWMinimum.Law
