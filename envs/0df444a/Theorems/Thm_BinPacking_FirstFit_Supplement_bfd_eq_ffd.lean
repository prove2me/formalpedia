-- Prove2me | Theorems.Thm_BinPacking_FirstFit_Supplement_bfd_eq_ffd
-- name    : BinPacking.FirstFit.Supplement.bfd_eq_ffd
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T11:39:37.625579+00:00
-- url     : https://prove2.me/theorems/4c89245d-2178-499e-b416-b1648a5b85c8
-- title:
--   Theorem 3.5 — if $L \subseteq [1/5, 1]$ then $BFD(L) = FFD(L)$
-- statement:
--   Let $L=(a_1,\dots,a_n)$ be a list of real numbers in $(0,1]$. Write $FFD(L)$ and $BFD(L)$ for the numbers of bins used by **first-fit decreasing** and **best-fit decreasing**: both arrange $L$ into nonincreasing order and then place the elements in that order into unit-capacity bins $B_1,B_2,\dots$; first-fit puts $a_i$ into the least-indexed bin whose level $\beta$ satisfies $\beta\le 1-a_i$, while best-fit puts it into the least-indexed bin among those with $\beta\le1-a_i$ and $\beta$ as large as possible.
--
--   **Theorem 3.5.** If every element of $L$ lies in $[1/5,1]$, then
--
--   $$
--   BFD(L)=FFD(L).
--   $$
--
--   Theorem 3.4 of the paper gives $BFD(L)\le FFD(L)$ when every element is at least $1/6$; Theorem 3.5 says that at or above $1/5$ the two decreasing rules always use the same number of bins. The paper notes that its Figs. 5 and 6 show the lower bounds $1/6$ and $1/5$ to be best possible. The paper does not prove Theorem 3.5; it refers to "a similar argument [6], [8]".
--
--   **Formalization Note** Lists are `List ℝ` with the standing hypothesis that every element is in $(0,1]$; "$L\subseteq[1/5,1]$" is the condition $1/5\le a$ on every element (the paper's footnote 2, p. 307: a list is a sequence, set notation is a convenience). $FFD$ and $BFD$ are those of the published definition `BinPacking.Decreasing.Model`: first-fit and best-fit run on a stable merge sort of $L$ into nonincreasing order, with new bins opened at the end; the bin count does not depend on how equal elements are ordered.
--
--   Differences from the source:
--   - encoding: "L ⊆ [1/5, 1]" → a list L of reals with every element in (0, 1] and every element ≥ 1/5; reason: the paper's lists are sequences of reals in (0, 1] (p. 300; footnote 2, p. 307), and the upper end 1 is already part of the standing hypothesis.
-- source:
--   Johnson, Demers, Ullman, Garey, Graham, Worst-Case Performance Bounds for Simple One-Dimensional Packing Algorithms, SIAM J. Comput. 3(4) (1974), p. 314, Theorem 3.5

import Mathlib
import Definitions.Def_BinPacking_Decreasing_Model

namespace BinPacking.FirstFit.Supplement

/-- Theorem 3.5 (Johnson et al. 1974, p. 314): if every element of the list `L` (of reals in
`(0, 1]`) lies in `[1/5, 1]`, then best-fit decreasing and first-fit decreasing use the same
number of bins, `BFD(L) = FFD(L)`. -/
theorem bfd_eq_ffd (L : List ℝ) (hL : BinPacking.Decreasing.IsList L)
    (h5 : ∀ a ∈ L, (1 / 5 : ℝ) ≤ a) :
    BinPacking.Decreasing.BFD L = BinPacking.Decreasing.FFD L := by sorry

end BinPacking.FirstFit.Supplement
