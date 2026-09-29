-- Prove2me | Theorems.Thm_BinPacking_Decreasing_ffd_position_order
-- name    : BinPacking.Decreasing.ffd_position_order
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T22:15:57.537487+00:00
-- url     : https://prove2.me/theorems/454ce251-dffc-4f1a-8a6c-88760c4cb293
-- title:
--   Claim 3.4.6 — among the FFD positions of elements at most $1/3$, the position order respects the list order
-- statement:
--   Let $L$ be a list of real numbers in $[1/6,1]$, let $a_1\ge\dots\ge a_n$ be $L$ in nonincreasing order, and let $PF$, $f_0$ and $h$ be as in Claim 3.4.5: $f_0(a_i)=(j,k)$ when $a_i$ is the $k$-th element of bin $j$ of the FFD packing, and $h$ is the largest index with $a_h>1/3$ ($0$ if there is none). Let $k_j$ be the number of elements of bin $j$ in $PF$. Order positions lexicographically:
--   $$(j,k)\le(j',k')\iff j<j'\ \text{ or }\ \bigl(j=j'\text{ and }k\le k'\bigr).$$
--
--   Let $S_h=\{f_0(a_i): i>h\}$ be the positions of $PF$ filled by elements after the $h$-th. If $(j,k),(j',k')\in S_h$, $k<k_j$ and $(j,k)\le(j',k')$, then
--   $$\operatorname{index}\bigl[f_0^{-1}(j,k)\bigr]\le\operatorname{index}\bigl[f_0^{-1}(j',k')\bigr].$$
--
--   In words: among elements at most $1/3$ that are not the last element of their FFD bin, an element in an earlier position of the FFD packing comes no later in the sorted list. The fact is used to show that BFD never needs a bin that FFD did not use.
--
--   **Formalization Note** The paper defines $S_h$ as the positions still empty after BFD has placed $a_1,\dots,a_h$; by Claim 3.4.5 these are exactly the FFD positions of $a_{h+1},\dots,a_n$, and the statement uses that description. It is phrased on items: for $0$-based items `i`, `i'` of $S=$ `sortDesc L` with index at least $h$ (the paper's $i>h$), whose FFD positions are (`binOf`, `slotOf`) ($0$-based bin and in-bin position), with `slotOf + 1` less than the size of the final bin (the paper's $k<k_j$) and lexicographically ordered positions, the conclusion is `i ≤ i'`.
-- source:
--   Johnson, Demers, Ullman, Garey, Graham, Worst-Case Performance Bounds for Simple One-Dimensional Packing Algorithms, SIAM J. Comput. 3(4) (1974), p. 313, Claim 3.4.6 (order on positions defined just before it; S_h defined p. 311)

import Mathlib
import Definitions.Def_BinPacking_Decreasing_Model

namespace BinPacking.Decreasing

/-- Claim 3.4.6 (p. 313), restated through Claim 3.4.5 (the positions of `S_h` are those that
the items after the first `h` fill in the FFD packing `PF`). Let `S = sortDesc L` with
`L ⊆ [1/6, 1]` and `h` the number of elements of `S` exceeding `1/3`. If items `i` and `i'`
of `S`, both after the first `h`, fill positions `(j, k)` and `(j', k')` of `PF`, the item
`i` is not the last one of its bin (`k < k_j`), and `(j, k) ≤ (j', k')` lexicographically,
then `i ≤ i'`. -/
theorem ffd_position_order (L : List ℝ) (hL : IsList L)
    (h6 : ∀ a ∈ L, (1 / 6 : ℝ) ≤ a) (i i' : Fin (sortDesc L).length)
    (hi : ((sortDesc L).filter (fun a => decide ((1 / 3 : ℝ) < a))).length ≤ (i : ℕ))
    (hi' : ((sortDesc L).filter (fun a => decide ((1 / 3 : ℝ) < a))).length ≤ (i' : ℕ))
    (hk : slotOf ffChoice (sortDesc L) i + 1 <
      ((run ffChoice (sortDesc L)).getD (binOf ffChoice (sortDesc L) i) []).length)
    (hle : binOf ffChoice (sortDesc L) i < binOf ffChoice (sortDesc L) i' ∨
      (binOf ffChoice (sortDesc L) i = binOf ffChoice (sortDesc L) i' ∧
        slotOf ffChoice (sortDesc L) i ≤ slotOf ffChoice (sortDesc L) i')) :
    i ≤ i' := by sorry

end BinPacking.Decreasing
