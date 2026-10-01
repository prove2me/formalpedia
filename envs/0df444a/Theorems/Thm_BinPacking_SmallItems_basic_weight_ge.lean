-- Prove2me | Theorems.Thm_BinPacking_SmallItems_basic_weight_ge
-- name    : BinPacking.SmallItems.basic_weight_ge
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T22:21:03.778511+00:00
-- url     : https://prove2.me/theorems/ffb69a58-60f4-441e-8c86-1d371858d0f5
-- title:
--   Claim 4.2.1 — the $w_1$-weight of BASIC is at least $FFD(L) - \sum_{j=2}^{N-1}(j-1)/j$
-- statement:
--   Let $N\ge 4$ be an integer and let $L$ be a list of real numbers all lying in $(1/N,1/2]$. Let BASIC be the set of elements of $L$ that are $k$-pieces lying in a $k$-bin of the First-Fit Decreasing packing of $L$, for some $k$. Then
--   $$\sum_{x\in \mathrm{BASIC}} w_1(x)\;\ge\; FFD(L)-\sum_{j=2}^{N-1}\frac{j-1}{j}.$$
--
--   This is the first half of Lemma 4.2: the elements of BASIC alone carry almost one unit of $w_1$-weight per FFD bin, the deficit being at most $(k-1)/k$ for one bin of each type $k$.
--
--   **Formalization Note** BASIC is a set of positions of the nonincreasing rearrangement of $L$ (definition `basic`), and $w_1$ is evaluated at the element in each position. The hypothesis $N\ge 4$ is the standing hypothesis of Lemma 4.2, within whose proof the claim is stated. The sum runs over the integers $j$ with $2\le j\le N-1$.
-- source:
--   Johnson, Demers, Ullman, Garey, Graham, Worst-Case Performance Bounds for Simple One-Dimensional Packing Algorithms, SIAM J. Comput. 3(4) (1974), p. 316, Claim 4.2.1

import Mathlib
import Definitions.Def_BinPacking_SmallItems_Model
import Definitions.Def_BinPacking_SmallItems_Weight

namespace BinPacking.SmallItems

/-- Claim 4.2.1 (p. 316): for an integer `N ≥ 4` (the standing hypothesis of Lemma 4.2) and
`L ⊆ (1/N, 1/2]`, `Σ_{x ∈ BASIC} w₁(x) ≥ FFD(L) − Σ_{j=2}^{N−1} (j − 1)/j`. -/
theorem basic_weight_ge (N : ℕ) (hN : 4 ≤ N) (L : List ℝ) (hL : IsList L)
    (hrange : ∀ a ∈ L, 1 / (N : ℝ) < a ∧ a ≤ 1 / 2) :
    ∑ i ∈ basic L, w1 ((sortDesc L).get i) ≥
      (FFD L : ℝ) - ∑ j ∈ Finset.Icc 2 (N - 1), ((j : ℝ) - 1) / (j : ℝ) := by sorry

end BinPacking.SmallItems
