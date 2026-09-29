-- Prove2me | Theorems.Thm_BinPacking_Decreasing_bfd_le_ffd
-- name    : BinPacking.Decreasing.bfd_le_ffd
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T22:16:26.405119+00:00
-- url     : https://prove2.me/theorems/ccbc83ae-d642-4478-ba12-c0c8cb82b24f
-- title:
--   Theorem 3.4 — if $L\subseteq[1/6,1]$ then $BFD(L)\le FFD(L)$
-- statement:
--   Let $L$ be a list of real numbers, every element of which lies in the closed interval $[1/6,1]$. Then Best-Fit Decreasing uses no more bins than First-Fit Decreasing:
--   $$BFD(L)\le FFD(L).$$
--
--   The lower endpoint $1/6$ cannot be lowered: the paper exhibits lists with elements below $1/6$ for which $BFD(L)=\tfrac{10}{9}FFD(L)$. Since every list in $(2/11,1]$ lies in $[1/6,1]$, the theorem lets the bound of Theorem 3.2 for BFD be derived from the bound for FFD on such lists.
-- source:
--   Johnson, Demers, Ullman, Garey, Graham, Worst-Case Performance Bounds for Simple One-Dimensional Packing Algorithms, SIAM J. Comput. 3(4) (1974), p. 310, Theorem 3.4

import Mathlib
import Definitions.Def_BinPacking_Decreasing_Model

namespace BinPacking.Decreasing

/-- Theorem 3.4 (p. 310): if every element of `L` lies in `[1/6, 1]`, then `BFD(L) ≤ FFD(L)`. -/
theorem bfd_le_ffd (L : List ℝ) (hL : IsList L) (h6 : ∀ a ∈ L, (1 / 6 : ℝ) ≤ a) :
    BFD L ≤ FFD L := by sorry

end BinPacking.Decreasing
