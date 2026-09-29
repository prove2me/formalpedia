-- Prove2me | Theorems.Thm_BinPacking_Decreasing_ffd_le_eleven_ninths_large_items
-- name    : BinPacking.Decreasing.ffd_le_eleven_ninths_large_items
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T22:17:26.109866+00:00
-- url     : https://prove2.me/theorems/f24d57b7-efa8-43d6-8dcb-615350c0c419
-- title:
--   Section 4, p. 314 — if $L\subseteq(2/11,1]$ then $FFD(L)\le\frac{11}{9}L^*+4$
-- statement:
--   Let $L$ be a list of real numbers each lying in the half-open interval $(2/11,1]$. Then First-Fit Decreasing satisfies
--   $$FFD(L)\le\frac{11}{9}\,L^*+4 .$$
--
--   This is the reduced form of Theorem 3.2 to which Section 3 of the paper brings the whole result: Lemma 3.3 (with $r=11/9$, $(r-1)/r=2/11$) shows that it suffices to consider lists in $(2/11,1]$, and Theorem 3.4 (since $(2/11,1]\subseteq[1/6,1]$) transfers the bound from FFD to BFD. The paper states it as "the crucial assertion" of Theorem 3.2 and gives an outline of its proof; the complete proof is in Johnson's 1973 thesis.
-- source:
--   Johnson, Demers, Ullman, Garey, Graham, Worst-Case Performance Bounds for Simple One-Dimensional Packing Algorithms, SIAM J. Comput. 3(4) (1974), p. 314, Section 4 (opening sentence); restated p. 322

import Mathlib
import Definitions.Def_BinPacking_Decreasing_Model

namespace BinPacking.Decreasing

/-- The reduced assertion of Section 4 (p. 314; restated p. 322): if every element of `L` lies
in `(2/11, 1]`, then `FFD(L) ≤ (11/9) L* + 4`. -/
theorem ffd_le_eleven_ninths_large_items (L : List ℝ) (hL : IsList L)
    (h211 : ∀ a ∈ L, (2 / 11 : ℝ) < a) :
    (FFD L : ℝ) ≤ (11 / 9 : ℝ) * (optBins L : ℝ) + 4 := by sorry

end BinPacking.Decreasing
