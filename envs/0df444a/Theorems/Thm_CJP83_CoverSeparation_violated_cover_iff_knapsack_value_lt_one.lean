-- Prove2me | Theorems.Thm_CJP83_CoverSeparation_violated_cover_iff_knapsack_value_lt_one
-- name    : CJP83.CoverSeparation.violated_cover_iff_knapsack_value_lt_one
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T02:36:44.421304+00:00
-- url     : https://prove2.me/theorems/dbbcabd4-dca0-4d16-ae6a-254d24fc4870
-- title:
--   p. 812, §2.3 — violated cover iff separation optimum is below one
-- statement:
--   Let $K$ be finite, $a_j>0$ rational, $a_0$ rational, and $0\le\bar x_j\le1$ for all $j$. Suppose the strict-cover problem (2.12) attains its minimum objective value $z$. Then
--   $$
--   \bigl(\exists\text{ a minimal cover }S:\ \sum_{j\in S}\bar x_j>|S|-1\bigr)
--   \quad\Longleftrightarrow\quad z<1.
--   $$
--   This is the paper's constraint identification equivalence: solving (2.12) detects a minimal cover inequality (2.7) that cuts off $\bar x$.
--
--   **Formalization Note** The paper takes $\bar x$ to be an LP-relaxation optimum, but this result uses only its unit-cube bounds. Existence of the optimal value is explicit: if no cover exists, (2.12) has no feasible point and no minimum. The strict knapsack constraint remains strict.
-- source:
--   Crowder, Johnson and Padberg, Solving Large-Scale Zero-One Linear Programming Problems, Operations Research 31 (1983), p. 812, Section 2.3, (2.7), (2.12), proof continues p. 813

import Mathlib
import Definitions.Def_CJP83_CoverSeparation_KnapsackRow

namespace CJP83.CoverSeparation

theorem violated_cover_iff_knapsack_value_lt_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℚ) (a₀ : ℚ) (hpos : ∀ j, 0 < a j)
    (xbar : ι → ℝ) (hcube : ∀ j, 0 ≤ xbar j ∧ xbar j ≤ 1)
    (z : ℝ) (hz : IsLeast (sepValues a a₀ xbar) z) :
    (∃ S : Finset ι, IsMinimalCover a a₀ S ∧
      (S.card : ℝ) - 1 < ∑ j ∈ S, xbar j) ↔ z < 1 := by sorry
end CJP83.CoverSeparation
