-- Prove2me | Theorems.Thm_BinPacking_FirstFit_early_items_exceed_coarseness
-- name    : BinPacking.FirstFit.early_items_exceed_coarseness
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T22:06:16.043826+00:00
-- url     : https://prove2.me/theorems/da7e5fd9-be1f-4575-93cf-f346b67b4142
-- title:
--   Claim 2.2.2 — elements placed before a bin is half full exceed its coarseness
-- statement:
--   Let $L$ be a list of reals in $(0,1]$, and run First-Fit (respectively Best-Fit) on $L$. Let $B$ be a bin of the completed packing and $\alpha$ its coarseness, the largest value $1-\operatorname{level}(B')$ over the bins $B'$ of smaller index (and $0$ for the first bin). If an element $a_i$ was placed into $B$ at a moment when the level of $B$ was at most $\tfrac12$, then
--
--   $$a_i>\alpha.$$
--
--   The claim holds for both algorithms, and the statement consists of the First-Fit and the Best-Fit version. It is the step that ties the on-line behaviour of the algorithms to the weight bound of Claim 2.2.3.
--
--   **Formalization Note** "Before $B$ was more than half full" is read as "the level of $B$ just before $a_i$ was placed was at most $\tfrac12$", which includes the element that opened the bin (level $0$). The coarseness is computed in the completed packing.
-- source:
--   Johnson, Demers, Ullman, Garey, Graham, Worst-Case Performance Bounds for Simple One-Dimensional Packing Algorithms, SIAM J. Comput. 3(4) (1974), p. 305, Claim 2.2.2

import Mathlib
import Definitions.Def_BinPacking_FirstFit_Model

namespace BinPacking.FirstFit

/-- Claim 2.2.2 (p. 305): in the completed FF packing (resp. BF packing) of `L`, every item
placed into a bin while that bin's level was at most `1/2` (i.e. before the bin was more than
half full) exceeds the coarseness of that bin. -/
theorem early_items_exceed_coarseness (L : List ℝ) (hL : IsList L) :
    (∀ i : Fin L.length, levelBefore ffChoice L i ≤ 1 / 2 →
        coarseness (ffPack L) (binOf ffChoice L i) < L.get i) ∧
    (∀ i : Fin L.length, levelBefore bfChoice L i ≤ 1 / 2 →
        coarseness (bfPack L) (binOf bfChoice L i) < L.get i) := by sorry

end BinPacking.FirstFit
