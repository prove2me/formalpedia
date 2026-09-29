-- Prove2me | Theorems.Thm_BinPacking_Decreasing_weight_ge_ffd_sub
-- name    : BinPacking.Decreasing.weight_ge_ffd_sub
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T22:17:01.383677+00:00
-- url     : https://prove2.me/theorems/c01631d6-b835-4a30-8c3a-4ced0b75ccb9
-- title:
--   Lemma 4.2 — for $N\ge 4$ and $L\subseteq(1/N,1/2]$, $W(L)\ge FFD(L)-N+2$
-- statement:
--   Let $N\ge 4$ be an integer and let $L$ be a list of real numbers each lying in $(1/N,1/2]$. Let $W$ be the weighting function of Section 4: $W(L)$ is the minimum, over all partitions $\pi$ of the elements of $L$ (arranged in nonincreasing order) into one- and two-element sets, of $\sum_{x\in\pi(1)}w_1(x)+\sum_{(x,y)\in\pi(2)}w_2(x,y)$. Then
--   $$W(L)\ \ge\ FFD(L)-N+2 .$$
--
--   The total weight of the list thus accounts for all but a bounded number of the bins used by First-Fit Decreasing. The paper uses it with $N=7$ for its $71/60$ bound, and with $N=6$ in the outline of Theorem 3.2, applied to the elements outside the bins of FFD whose largest element exceeds $1/2$.
-- source:
--   Johnson, Demers, Ullman, Garey, Graham, Worst-Case Performance Bounds for Simple One-Dimensional Packing Algorithms, SIAM J. Comput. 3(4) (1974), p. 316, Lemma 4.2 (W defined pp. 315-317)

import Mathlib
import Definitions.Def_BinPacking_Decreasing_Model
import Definitions.Def_BinPacking_Decreasing_Weight

namespace BinPacking.Decreasing

/-- Lemma 4.2 (p. 316): for any integer `N ≥ 4` and any list `L` with every element in
`(1/N, 1/2]`, `W(L) ≥ FFD(L) − N + 2`. -/
theorem weight_ge_ffd_sub (N : ℕ) (hN : 4 ≤ N) (L : List ℝ) (hL : IsList L)
    (hrange : ∀ a ∈ L, 1 / (N : ℝ) < a ∧ a ≤ 1 / 2) :
    W L ≥ (FFD L : ℝ) - (N : ℝ) + 2 := by sorry

end BinPacking.Decreasing
