-- Prove2me | Theorems.Thm_BinPacking_SmallItems_W_flatten_le_sum
-- name    : BinPacking.SmallItems.W_flatten_le_sum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T22:22:49.18568+00:00
-- url     : https://prove2.me/theorems/2f8cf4ab-a1ad-42b4-bbaa-dae86bc39e45
-- title:
--   Subadditivity of $W$: $W(X_1 \cup \dots \cup X_k) \le \sum_i W(X_i)$
-- statement:
--   Let $X_1,\dots,X_k$ be finite lists of real numbers in $(0,1]$, regarded as disjoint parts of their union $X_1\cup\dots\cup X_k$ (the concatenation of the lists, counted with multiplicity). Then
--   $$W\Bigl(\bigcup_{i=1}^k X_i\Bigr)\;\le\;\sum_{i=1}^k W(X_i).$$
--
--   Applied to the bins $X_1,\dots,X_{L^*}$ of an optimal packing of $L$, subadditivity bounds $W(L)$ by the sum of the weights of the bins, which is how the per-bin bound of Lemma 4.3 becomes a bound on $W(L)$.
--
--   **Formalization Note** The parts are a list `Xs : List (List ℝ)` and the union is `Xs.flatten`. The hypothesis that all elements lie in $(0,1]$ is the paper's standing assumption on the elements of $L$.
-- source:
--   Johnson, Demers, Ullman, Garey, Graham, Worst-Case Performance Bounds for Simple One-Dimensional Packing Algorithms, SIAM J. Comput. 3(4) (1974), p. 316, Section 4 (subadditivity of W)

import Mathlib
import Definitions.Def_BinPacking_SmallItems_Model
import Definitions.Def_BinPacking_SmallItems_Weight

namespace BinPacking.SmallItems

/-- Subadditivity of `W` (Section 4, p. 316): `W(X₁ ∪ ⋯ ∪ X_k) ≤ Σ W(X_i)`, for disjoint parts `X_i`
of a list of reals in `(0, 1]`, the union being the concatenation of the parts. -/
theorem W_flatten_le_sum (Xs : List (List ℝ)) (hL : IsList Xs.flatten) :
    W Xs.flatten ≤ (Xs.map W).sum := by sorry

end BinPacking.SmallItems
