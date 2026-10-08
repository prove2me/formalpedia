-- Prove2me | Theorems.Thm_CJP83_CoverSeparation_cover_inequality_valid
-- name    : CJP83.CoverSeparation.cover_inequality_valid
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T02:36:07.491868+00:00
-- url     : https://prove2.me/theorems/06c4e370-11b0-4a12-97e2-3121ff4cefc1
-- title:
--   p. 810, (2.7) — validity of the minimal cover inequality
-- statement:
--   Let $K$ be finite, with positive rational weights $a_j$ and rational capacity $a_0$. If $S\subseteq K$ is a minimal cover of (2.5), then every feasible zero–one vector $x$ satisfies
--   $$
--   \sum_{j\in S}x_j\le |S|-1.
--   $$
--   This is the validity claim for inequality (2.7), used before the paper lifts cover inequalities to other variables. The same bound holds for any cover, though the paper states it here for minimal covers.
-- source:
--   Crowder, Johnson and Padberg, Solving Large-Scale Zero-One Linear Programming Problems, Operations Research 31 (1983), p. 810, Section 2.2, (2.7)

import Mathlib
import Definitions.Def_CJP83_CoverSeparation_KnapsackRow

namespace CJP83.CoverSeparation

theorem cover_inequality_valid {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℚ) (a₀ : ℚ) (hpos : ∀ j, 0 < a j)
    (S x : Finset ι) (hcover : IsMinimalCover a a₀ S)
    (hx : IsRowFeasible a a₀ x) :
    (∑ j ∈ S, binaryValue x j) ≤ (S.card : ℝ) - 1 := by sorry
end CJP83.CoverSeparation
