-- Prove2me | Theorems.Thm_CJP83_CoverSeparation_knapsack_optimum_has_minimal_cover
-- name    : CJP83.CoverSeparation.knapsack_optimum_has_minimal_cover
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T02:36:34.463954+00:00
-- url     : https://prove2.me/theorems/a3274ac5-4b11-4c84-96d9-2bfecfe0261f
-- title:
--   pp. 812–813, §2.3 — an optimum can be a minimal cover
-- statement:
--   Let $0\le\bar x_j\le1$ for every $j\in K$, and suppose the strict-cover problem (2.12) has minimum value $z$. For positive rational row weights, there is a minimal cover $S$ of (2.5) whose separation objective equals that minimum:
--   $$
--   \sum_{j\in S}(1-\bar x_j)=z.
--   $$
--   The claim is the reverse direction's central assertion, which begins on p. 812 and continues on p. 813. Nonnegative objective coefficients allow a cover to be reduced without increasing its objective. The paper calls the resulting inequality a “minimum cover” on p. 813; here minimality has its (2.6) meaning.
-- source:
--   Crowder, Johnson and Padberg, Solving Large-Scale Zero-One Linear Programming Problems, Operations Research 31 (1983), pp. 812–813, Section 2.3, (2.12), reverse direction

import Mathlib
import Definitions.Def_CJP83_CoverSeparation_KnapsackRow

namespace CJP83.CoverSeparation

theorem knapsack_optimum_has_minimal_cover
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℚ) (a₀ : ℚ) (hpos : ∀ j, 0 < a j)
    (xbar : ι → ℝ) (hcube : ∀ j, 0 ≤ xbar j ∧ xbar j ≤ 1)
    (z : ℝ) (hz : IsLeast (sepValues a a₀ xbar) z) :
    ∃ S : Finset ι, IsMinimalCover a a₀ S ∧
      (∑ j ∈ S, (1 - xbar j)) = z := by sorry
end CJP83.CoverSeparation
