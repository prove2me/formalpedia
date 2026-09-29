-- Prove2me | Theorems.Thm_BinPacking_SmallItems_ffd_le_seventy_one_sixtieths
-- name    : BinPacking.SmallItems.ffd_le_seventy_one_sixtieths
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T22:23:50.141631+00:00
-- url     : https://prove2.me/theorems/4c187921-2eaf-4ae2-9104-ffbc77963d91
-- title:
--   Theorem 4.1 — for $L \subseteq (0, 1/2]$, $FFD(L) \le (71/60)L^* + 5$
-- statement:
--   Let $L$ be a list of real numbers, each lying in $(0,1/2]$, and let $L^*$ be the minimum number of unit-capacity bins into which $L$ can be packed. Then First-Fit Decreasing uses
--   $$FFD(L)\;\le\;\frac{71}{60}\,L^*+5$$
--   bins.
--
--   The constant $71/60$ is best possible: the Remark after the theorem gives lists with $FFD(L)=\tfrac{71}{60}L^*$ whose elements are all below $1/3$. The theorem is the model case of the weighting-function method that proves the general $11/9$ bound for FFD.
--
--   **Formalization Note** $FFD(L)$ is First-Fit applied to the nonincreasing rearrangement of $L$, and $L^*$ is `optBins L`; see the model definition file.
-- source:
--   Johnson, Demers, Ullman, Garey, Graham, Worst-Case Performance Bounds for Simple One-Dimensional Packing Algorithms, SIAM J. Comput. 3(4) (1974), p. 314, Theorem 4.1

import Mathlib
import Definitions.Def_BinPacking_SmallItems_Model

namespace BinPacking.SmallItems

/-- Theorem 4.1 (p. 314): for all lists `L ⊆ (0, 1/2]`, `FFD(L) ≤ (71/60)L* + 5`. -/
theorem ffd_le_seventy_one_sixtieths (L : List ℝ) (hL : IsList L) (hhalf : ∀ a ∈ L, a ≤ 1 / 2) :
    (FFD L : ℝ) ≤ 71 / 60 * (optBins L : ℝ) + 5 := by sorry

end BinPacking.SmallItems
