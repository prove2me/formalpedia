-- Prove2me | Theorems.Thm_BinPacking_SmallItems_ffd_filter_preserves_excess
-- name    : BinPacking.SmallItems.ffd_filter_preserves_excess
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T22:20:21.944379+00:00
-- url     : https://prove2.me/theorems/e3877310-fc32-4812-afbe-11a01bd5398f
-- title:
--   Lemma 3.3 (FFD part) — deleting elements not exceeding $(r-1)/r$ preserves $FFD(L) > rL^* + d$
-- statement:
--   Let $L$ be a list of real numbers in $(0,1]$ and let $r\ge 1$, $d\ge 1$ be real numbers. Let $L'$ be the list obtained from $L$ by deleting every element not exceeding $(r-1)/r$. If
--   $$FFD(L) > r\,L^* + d,$$
--   then also
--   $$FFD(L') > r\,L'^* + d .$$
--
--   The lemma reduces worst-case upper bounds of the form $FFD(L)\le rL^*+d$ to lists whose elements all exceed $(r-1)/r$. With $r=71/60$ and $d=5$ the threshold is $11/71>1/7$, which is how the proof of the $71/60$ bound restricts attention to lists in $(1/7,1/2]$.
--
--   **Formalization Note** $L'$ is `L.filter (fun a => (r - 1) / r < a)`, which keeps the order of the remaining elements. Only the First-Fit Decreasing half of the paper's lemma is stated; the Best-Fit Decreasing half is not used in this mission.
-- source:
--   Johnson, Demers, Ullman, Garey, Graham, Worst-Case Performance Bounds for Simple One-Dimensional Packing Algorithms, SIAM J. Comput. 3(4) (1974), p. 309, Lemma 3.3 (FFD part)

import Mathlib
import Definitions.Def_BinPacking_SmallItems_Model

namespace BinPacking.SmallItems

/-- Lemma 3.3, FFD part (p. 309): if `FFD(L) > rL* + d` with `r, d ≥ 1`, then the list `L′`
obtained from `L` by deleting all elements not exceeding `(r − 1)/r` also has
`FFD(L′) > rL′* + d`. -/
theorem ffd_filter_preserves_excess (r d : ℝ) (hr : 1 ≤ r) (hd : 1 ≤ d) (L : List ℝ)
    (hL : IsList L) (h : r * (optBins L : ℝ) + d < (FFD L : ℝ)) :
    r * (optBins (L.filter (fun a => decide ((r - 1) / r < a))) : ℝ) + d <
      (FFD (L.filter (fun a => decide ((r - 1) / r < a))) : ℝ) := by sorry

end BinPacking.SmallItems
