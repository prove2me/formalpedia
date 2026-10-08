-- Prove2me | Theorems.Thm_CJP83_CoverSeparation_configuration_inequality_valid
-- name    : CJP83.CoverSeparation.configuration_inequality_valid
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T02:36:15.92656+00:00
-- url     : https://prove2.me/theorems/78fcf277-4be1-4b38-96ae-b957354336d3
-- title:
--   p. 811, (2.9) — validity of configuration inequalities
-- statement:
--   Let $S^*\subseteq K$, $t\notin S^*$ and $2\le k\le |S^*|$ form a $(1,k)$-configuration for the positive-weight row (2.5): $\sum_{j\in S^*}a_j\le a_0$ and every $k$-element subset $Q\subseteq S^*$ makes $Q\cup\{t\}$ a minimal cover. For each integer $r$ with $k\le r\le |S^*|$ and each $T\subseteq S^*$ of size $r$, every feasible zero–one vector $x$ satisfies
--   $$
--   (r-k+1)x_t+\sum_{j\in T}x_j\le r.
--   $$
--   These are all the inequalities in (2.9), including the cases $r=k$ and $r=|S^*|$.
-- source:
--   Crowder, Johnson and Padberg, Solving Large-Scale Zero-One Linear Programming Problems, Operations Research 31 (1983), p. 811, Section 2.2, (2.8)–(2.9)

import Mathlib
import Definitions.Def_CJP83_CoverSeparation_KnapsackRow

namespace CJP83.CoverSeparation

theorem configuration_inequality_valid {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℚ) (a₀ : ℚ) (hpos : ∀ j, 0 < a j)
    (Sstar : Finset ι) (t : ι) (k r : ℕ)
    (hconfig : IsOneKConfiguration a a₀ Sstar t k)
    (hr₁ : k ≤ r) (hr₂ : r ≤ Sstar.card)
    (T x : Finset ι) (hT₁ : T ⊆ Sstar) (hT₂ : T.card = r)
    (hx : IsRowFeasible a a₀ x) :
    ((r : ℝ) - (k : ℝ) + 1) * binaryValue x t +
      ∑ j ∈ T, binaryValue x j ≤ (r : ℝ) := by sorry
end CJP83.CoverSeparation
