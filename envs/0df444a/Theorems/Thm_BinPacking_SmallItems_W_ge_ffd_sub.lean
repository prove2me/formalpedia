-- Prove2me | Theorems.Thm_BinPacking_SmallItems_W_ge_ffd_sub
-- name    : BinPacking.SmallItems.W_ge_ffd_sub
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T22:22:17.272954+00:00
-- url     : https://prove2.me/theorems/9ce81529-11e1-4b95-ae78-9681e6aadb55
-- title:
--   Lemma 4.2 — $W(L) \ge FFD(L) - N + 2$ for $L \subseteq (1/N, 1/2]$
-- statement:
--   Let $N\ge 4$ be an integer and let $L$ be a list of real numbers all lying in $(1/N,1/2]$. Then the weight of $L$ satisfies
--   $$W(L)\;\ge\; FFD(L)-N+2 .$$
--
--   This is the first half of the weighting argument: the total weight of the list falls short of the number of FFD bins by at most a constant depending on $N$. With $N=7$ it gives $FFD(L)-5\le W(L)$ for lists in $(1/7,1/2]$.
--
--   **Formalization Note** $W$ is the minimum of $w_{12}(\pi)$ over all partitions of $L$ into one- and two-element sets, with the elements indexed in nonincreasing order; see the definition file.
-- source:
--   Johnson, Demers, Ullman, Garey, Graham, Worst-Case Performance Bounds for Simple One-Dimensional Packing Algorithms, SIAM J. Comput. 3(4) (1974), p. 316, Lemma 4.2

import Mathlib
import Definitions.Def_BinPacking_SmallItems_Model
import Definitions.Def_BinPacking_SmallItems_Weight

namespace BinPacking.SmallItems

/-- Lemma 4.2 (p. 316): for any integer `N ≥ 4` and `L ⊆ (1/N, 1/2]`, `W(L) ≥ FFD(L) − N + 2`. -/
theorem W_ge_ffd_sub (N : ℕ) (hN : 4 ≤ N) (L : List ℝ) (hL : IsList L)
    (hrange : ∀ a ∈ L, 1 / (N : ℝ) < a ∧ a ≤ 1 / 2) :
    W L ≥ (FFD L : ℝ) - (N : ℝ) + 2 := by sorry

end BinPacking.SmallItems
