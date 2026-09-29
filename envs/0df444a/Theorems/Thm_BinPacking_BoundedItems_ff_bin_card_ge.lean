-- Prove2me | Theorems.Thm_BinPacking_BoundedItems_ff_bin_card_ge
-- name    : BinPacking.BoundedItems.ff_bin_card_ge
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T22:11:09.598951+00:00
-- url     : https://prove2.me/theorems/bfb98bf0-3e0d-4aeb-be8a-79451277f40b
-- title:
--   Proof of Theorem 2.3 — every First-Fit bin but the last holds at least m items when no item exceeds 1/m
-- statement:
--   Let $m\ge 1$ be an integer and let $L=(a_1,\dots,a_n)$ be a list of numbers in $(0,1]$ none of which exceeds $\frac1m$. Consider the First-Fit packing $B_1,\dots,B_{FF(L)}$ of $L$. Then
--   $$|B_j|\ \ge\ m\qquad\text{for every } j<FF(L),$$
--   that is, every bin except possibly the last one contains at least $m$ elements.
--
--   This is the first step of the paper's proof of the upper bound in Theorem 2.3(ii): it is what guarantees that a lightly filled bin must contain a small element.
--
--   **Formalization Note** The bins are the list `ffPack L` in the order they were opened; "every bin except the last" is `(ffPack L).dropLast`, and the number of elements of a bin is the length of its contents list. The step is stated under the proof's own hypothesis "no element exceeding $1/m$", which is weaker than $L\subseteq(0,\alpha]$ with $m=\lfloor\alpha^{-1}\rfloor$.
-- source:
--   Johnson, Demers, Ullman, Garey, Graham, Worst-Case Performance Bounds for Simple One-Dimensional Packing Algorithms, SIAM J. Comput. 3(4) (1974), p. 308, Section 2, proof of Theorem 2.3

import Mathlib
import Definitions.Def_BinPacking_BoundedItems_Model

namespace BinPacking.BoundedItems

/-- Johnson et al. 1974, Section 2, proof of Theorem 2.3, p. 308: if no element of `L`
exceeds `1/m` (`m ≥ 1` an integer), then every bin of the First-Fit packing of `L`, except
possibly the last bin, contains at least `m` elements. -/
theorem ff_bin_card_ge (m : ℕ) (hm : 1 ≤ m) (L : List ℝ) (hL : IsList L)
    (hLm : ∀ a ∈ L, a ≤ 1 / (m : ℝ)) :
    ∀ B ∈ (ffPack L).dropLast, m ≤ B.length := by sorry

end BinPacking.BoundedItems
