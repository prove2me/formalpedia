-- Prove2me | Theorems.Thm_BinPacking_Decreasing_ffd_bfd_le_eleven_ninths
-- name    : BinPacking.Decreasing.ffd_bfd_le_eleven_ninths
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T22:18:32.717649+00:00
-- url     : https://prove2.me/theorems/ab01bc6f-6cfa-47c8-a1e3-4b14b9435e22
-- title:
--   Theorem 3.2 — $FFD(L)\le\frac{11}{9}L^*+4$ and $BFD(L)\le\frac{11}{9}L^*+4$ for all lists $L$
-- statement:
--   Let $L=(a_1,\dots,a_n)$ be any list of real numbers in $(0,1]$, and let $L^*$ be the minimum number of unit-capacity bins into which its elements can be packed. Then First-Fit Decreasing and Best-Fit Decreasing both use at most $\tfrac{11}{9}L^*+4$ bins:
--   $$FFD(L)\le\frac{11}{9}\,L^*+4\qquad\text{and}\qquad BFD(L)\le\frac{11}{9}\,L^*+4 .$$
--
--   Together with the matching lower bound (Theorem 3.1) this gives the asymptotic worst-case ratio $\lim_{k\to\infty}R_{FFD}(k)=\lim_{k\to\infty}R_{BFD}(k)=11/9$ of the two decreasing heuristics, the headline result of the paper.
--
--   **Formalization Note** $FFD(L)$ and $BFD(L)$ are computed on $L$ arranged into nonincreasing order by the mission's sort; the statement holds for every list $L$, sorted or not. The constants $11/9$ and $4$ are exactly the paper's.
-- source:
--   Johnson, Demers, Ullman, Garey, Graham, Worst-Case Performance Bounds for Simple One-Dimensional Packing Algorithms, SIAM J. Comput. 3(4) (1974), p. 308, Theorem 3.2

import Mathlib
import Definitions.Def_BinPacking_Decreasing_Model

namespace BinPacking.Decreasing

/-- Theorem 3.2 (p. 308): for every list `L` of reals in `(0, 1]`,
`FFD(L) ≤ (11/9) L* + 4` and `BFD(L) ≤ (11/9) L* + 4`. -/
theorem ffd_bfd_le_eleven_ninths (L : List ℝ) (hL : IsList L) :
    (FFD L : ℝ) ≤ (11 / 9 : ℝ) * (optBins L : ℝ) + 4 ∧
      (BFD L : ℝ) ≤ (11 / 9 : ℝ) * (optBins L : ℝ) + 4 := by sorry

end BinPacking.Decreasing
