-- Prove2me | Theorems.Thm_BinPacking_BoundedItems_ff_light_bins_le_two
-- name    : BinPacking.BoundedItems.ff_light_bins_le_two
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T22:11:42.806674+00:00
-- url     : https://prove2.me/theorems/49c4899d-3a83-46b6-bad1-ba25296e010a
-- title:
--   Proof of Theorem 2.3 — all but at most two First-Fit bins are filled to level at least m/(m+1)
-- statement:
--   Let $m\ge 1$ be an integer and let $L$ be a list of numbers in $(0,1]$ none of which exceeds $\frac1m$. In the First-Fit packing of $L$, the number of bins whose level (sum of contents) is below $\frac{m}{m+1}$ is at most two:
--   $$\#\Big\{\,j : \sum_{a\in B_j} a<\frac{m}{m+1}\Big\}\ \le\ 2.$$
--
--   Summing levels then gives $L^*\ge w(L)\ge\frac{m}{m+1}\,(FF(L)-2)$, where $w(L)$ is the total size of $L$; this is how the paper derives Theorem 2.3(ii) for First-Fit.
--
--   **Formalization Note** The count is the length of the sublist of `ffPack L` of bins with `level B < m/(m+1)`, computed in `ℝ`. The hypothesis is the proof's "no element exceeding $1/m$".
-- source:
--   Johnson, Demers, Ullman, Garey, Graham, Worst-Case Performance Bounds for Simple One-Dimensional Packing Algorithms, SIAM J. Comput. 3(4) (1974), p. 308, Section 2, proof of Theorem 2.3

import Mathlib
import Definitions.Def_BinPacking_BoundedItems_Model

namespace BinPacking.BoundedItems

/-- Johnson et al. 1974, Section 2, proof of Theorem 2.3, p. 308: if no element of `L`
exceeds `1/m` (`m ≥ 1` an integer), then all but at most two bins of the First-Fit packing
of `L` contain elements totaling at least `m/(m + 1)`. -/
theorem ff_light_bins_le_two (m : ℕ) (hm : 1 ≤ m) (L : List ℝ) (hL : IsList L)
    (hLm : ∀ a ∈ L, a ≤ 1 / (m : ℝ)) :
    ((ffPack L).filter (fun B => decide (level B < (m : ℝ) / (m + 1)))).length ≤ 2 := by sorry

end BinPacking.BoundedItems
