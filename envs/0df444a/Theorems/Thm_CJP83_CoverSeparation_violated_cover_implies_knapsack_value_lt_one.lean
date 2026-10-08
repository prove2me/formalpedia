-- Prove2me | Theorems.Thm_CJP83_CoverSeparation_violated_cover_implies_knapsack_value_lt_one
-- name    : CJP83.CoverSeparation.violated_cover_implies_knapsack_value_lt_one
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T02:36:23.673579+00:00
-- url     : https://prove2.me/theorems/dff5da00-f98b-4b32-8035-cc36cbca7cc0
-- title:
--   p. 812, §2.3 — a violated cover gives a separation value below one
-- statement:
--   Let $S$ be a minimal cover for a positive-weight row (2.5), and let $\bar x$ be a real vector. Suppose the minimum $z$ of the strict-cover separation problem (2.12) exists. If the cover inequality cuts off $\bar x$, then
--   $$
--   \sum_{j\in S}\bar x_j>|S|-1\quad\Longrightarrow\quad z<1.
--   $$
--   This is the forward direction of the paper's separation equivalence. It does not use bounds on $\bar x$; the minimum hypothesis means that (2.12) has an attained feasible value.
-- source:
--   Crowder, Johnson and Padberg, Solving Large-Scale Zero-One Linear Programming Problems, Operations Research 31 (1983), p. 812, Section 2.3, (2.7), (2.12), forward direction

import Mathlib
import Definitions.Def_CJP83_CoverSeparation_KnapsackRow

namespace CJP83.CoverSeparation

theorem violated_cover_implies_knapsack_value_lt_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℚ) (a₀ : ℚ) (hpos : ∀ j, 0 < a j)
    (xbar : ι → ℝ) (z : ℝ) (hz : IsLeast (sepValues a a₀ xbar) z)
    (S : Finset ι) (hcover : IsMinimalCover a a₀ S)
    (hviolated : (S.card : ℝ) - 1 < ∑ j ∈ S, xbar j) :
    z < 1 := by sorry
end CJP83.CoverSeparation
