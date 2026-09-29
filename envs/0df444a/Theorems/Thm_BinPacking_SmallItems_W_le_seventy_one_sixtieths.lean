-- Prove2me | Theorems.Thm_BinPacking_SmallItems_W_le_seventy_one_sixtieths
-- name    : BinPacking.SmallItems.W_le_seventy_one_sixtieths
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T22:23:16.351612+00:00
-- url     : https://prove2.me/theorems/6c9b70f9-e37d-4038-bd5d-5f8d371ecc82
-- title:
--   Lemma 4.3 — a set $X \subseteq (1/7, 1/2]$ with sum at most 1 has $W(X) \le 71/60$
-- statement:
--   Let $X$ be a finite list of real numbers, each lying in $(1/7,1/2]$, whose sum does not exceed $1$. Then
--   $$W(X)\;\le\;\frac{71}{60}.$$
--
--   This is the second half of the weighting argument: every legally packed bin carries weight at most $71/60$. The bound is attained, for instance, by a bin of the optimal packing in the paper's Fig. 8 (one $3$-piece, one $4$-piece and three $5$-pieces).
--
--   **Formalization Note** $X$ is a `List ℝ`, so repeated values are allowed; $W$ is the minimum of $w_{12}$ over partitions of $X$ into one- and two-element sets.
-- source:
--   Johnson, Demers, Ullman, Garey, Graham, Worst-Case Performance Bounds for Simple One-Dimensional Packing Algorithms, SIAM J. Comput. 3(4) (1974), p. 316, Lemma 4.3

import Mathlib
import Definitions.Def_BinPacking_SmallItems_Model
import Definitions.Def_BinPacking_SmallItems_Weight

namespace BinPacking.SmallItems

/-- Lemma 4.3 (p. 316): if `X ⊆ (1/7, 1/2]` is any set of elements whose sum does not exceed `1`,
then `W(X) ≤ 71/60`. -/
theorem W_le_seventy_one_sixtieths (X : List ℝ) (hX : ∀ x ∈ X, 1 / 7 < x ∧ x ≤ 1 / 2)
    (hsum : X.sum ≤ 1) :
    W X ≤ 71 / 60 := by sorry

end BinPacking.SmallItems
