-- Prove2me | Theorems.Thm_BinPacking_SmallItems_w12_ge_basic_weight
-- name    : BinPacking.SmallItems.w12_ge_basic_weight
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T22:21:43.652458+00:00
-- url     : https://prove2.me/theorems/998ce8a1-84cd-4c7d-aef8-4c71c335d8b1
-- title:
--   Claim 4.2.2 — every partition $\pi$ has $w_{12}(\pi) \ge w_1(\mathrm{BASIC}) - \sum_{j=3}^{N-1} 1/j$
-- statement:
--   Let $N\ge 4$ be an integer, let $L$ be a list of real numbers all lying in $(1/N,1/2]$, and let $\pi$ be any partition of $L$ into one- and two-element sets. Then
--   $$w_{12}(\pi)\;\ge\; w_1(\mathrm{BASIC})-\sum_{j=3}^{N-1}\frac1j,$$
--   where $w_1(\mathrm{BASIC})=\sum_{x\in\mathrm{BASIC}}w_1(x)$ and BASIC is taken with respect to the First-Fit Decreasing packing of $L$.
--
--   The claim says that the discounts granted by $w_2$ on the pairs of any partition are paid for, up to a bounded error, by the $w_1$-weight of the SURPLUS elements. Together with Claim 4.2.1 it gives Lemma 4.2.
--
--   **Formalization Note** The elements of $L$ are indexed by the positions of its nonincreasing rearrangement `sortDesc L`, and $\pi$ is an arbitrary involution of those positions (a member of `pairings`), with $w_{12}$ computed as in the definition of $W$. The sum runs over the integers $j$ with $3\le j\le N-1$.
-- source:
--   Johnson, Demers, Ullman, Garey, Graham, Worst-Case Performance Bounds for Simple One-Dimensional Packing Algorithms, SIAM J. Comput. 3(4) (1974), p. 317, Claim 4.2.2

import Mathlib
import Definitions.Def_BinPacking_SmallItems_Model
import Definitions.Def_BinPacking_SmallItems_Weight

namespace BinPacking.SmallItems

/-- Claim 4.2.2 (p. 317): if `N ≥ 4` and `π` is a partition of `L ⊆ (1/N, 1/2]` into one- and
two-element sets, then `w₁₂(π) ≥ w₁(BASIC) − Σ_{j=3}^{N−1} 1/j`. The partition is any involution of
the positions of the nonincreasing rearrangement of `L`. -/
theorem w12_ge_basic_weight (N : ℕ) (hN : 4 ≤ N) (L : List ℝ) (hL : IsList L)
    (hrange : ∀ a ∈ L, 1 / (N : ℝ) < a ∧ a ≤ 1 / 2)
    (σ : Equiv.Perm (Fin (sortDesc L).length)) (hσ : σ ∈ pairings (sortDesc L).length) :
    w12 (sortDesc L) σ ≥
      ∑ i ∈ basic L, w1 ((sortDesc L).get i) - ∑ j ∈ Finset.Icc 3 (N - 1), 1 / (j : ℝ) := by sorry

end BinPacking.SmallItems
