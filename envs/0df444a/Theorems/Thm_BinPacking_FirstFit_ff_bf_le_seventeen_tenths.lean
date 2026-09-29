-- Prove2me | Theorems.Thm_BinPacking_FirstFit_ff_bf_le_seventeen_tenths
-- name    : BinPacking.FirstFit.ff_bf_le_seventeen_tenths
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T22:07:47.386014+00:00
-- url     : https://prove2.me/theorems/aa8deb35-ab00-4920-8367-4ccaf1c85f62
-- title:
--   Theorem 2.2 — $FF(L)\le 1.7L^*+2$ and $BF(L)\le 1.7L^*+2$
-- statement:
--   For every list $L=(a_1,\dots,a_n)$ of real numbers in $(0,1]$, with $L^*$ the minimum number of unit bins needed to pack $L$,
--
--   $$FF(L)\le 1.7\,L^*+2\qquad\text{and}\qquad BF(L)\le 1.7\,L^*+2.$$
--
--   This is the upper half of the asymptotic worst-case ratio $\tfrac{17}{10}$ of First-Fit and Best-Fit: the additive constant $2$ is independent of the list.
-- source:
--   Johnson, Demers, Ullman, Garey, Graham, Worst-Case Performance Bounds for Simple One-Dimensional Packing Algorithms, SIAM J. Comput. 3(4) (1974), p. 304, Theorem 2.2

import Mathlib
import Definitions.Def_BinPacking_FirstFit_Model

namespace BinPacking.FirstFit

/-- Theorem 2.2 (p. 304): for every list `L` of reals in `(0, 1]`,
`FF(L) ≤ 1.7 L* + 2` and `BF(L) ≤ 1.7 L* + 2`. -/
theorem ff_bf_le_seventeen_tenths (L : List ℝ) (hL : IsList L) :
    (FF L : ℝ) ≤ 17 / 10 * (optBins L : ℝ) + 2 ∧
    (BF L : ℝ) ≤ 17 / 10 * (optBins L : ℝ) + 2 := by sorry

end BinPacking.FirstFit
