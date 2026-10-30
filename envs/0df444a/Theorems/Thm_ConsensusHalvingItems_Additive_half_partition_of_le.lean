-- Prove2me | Theorems.Thm_ConsensusHalvingItems_Additive_half_partition_of_le
-- name    : ConsensusHalvingItems.Additive.half_partition_of_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:36:14.190637+00:00
-- url     : https://prove2.me/theorems/0c552748-2bcf-4782-b9cf-3c514415af36
-- title:
--   Proof of Theorem 2.2: the case $n \ge m$
-- statement:
--   Let $n$ agents have additive utilities over $m$ items with $n \ge m$. The partition that divides every item in half, $x_j = 1/2$ for all $j$, is a consensus halving, and it cuts exactly
--
--   $$
--   m = \min\{n, m\}
--   $$
--
--   items. This settles Theorem 2.2 when there are at least as many agents as items.
--
--   Differences from the source:
--   - reading: real utilities ui(j) (no encoding fixed) → rational values u : Fin n → Fin m → ℚ; reason: an algorithm takes encoded input; reals have no finite encoding (Reading 2)
--   - generalization: nonnegative utilities; N = [n], M = [m] for positive n, m → values of any sign; n = 0 and m = 0 allowed; reason: the p. 6 remark extends the algorithm to negative values; the statement specializes to nonnegative values and positive n, m
--   - encoding: partition (M1, M2) of the items M = [m]; agents N = [n] → (x, 1 − x) with x : Fin m → ℚ; 0-based Fin n, Fin m; reason: a two-part partition is determined by its first part; same instances
-- source:
--   Goldberg, Hollender, Igarashi, Manurangsi, Suksompong, Consensus Halving for Sets of Items, arXiv:2007.06754v1, proof of Theorem 2.2, ¶1, p. 5

import Mathlib
import Definitions.Def_ConsensusHalvingItems_Additive_IsConsensusHalving
import Definitions.Def_ConsensusHalvingItems_Additive_numCuts

namespace ConsensusHalvingItems.Additive

/-- **The case n ≥ m: halve every item.**
Goldberg, Hollender, Igarashi, Manurangsi, Suksompong, *Consensus Halving for Sets of Items*,
arXiv:2007.06754v1, proof of Theorem 2.2, ¶1, p. 5: "If n ≥ m, a partition that divides
every item in half is clearly a consensus halving and makes m = min{n, m} cuts."

If `m ≤ n`, the point `x_j = 1/2` for every item `j` is a consensus halving for every value
matrix `u`, and it cuts exactly `min n m` items.

**Formalization Note.** Partition `(x, 1 - x)`; 0-based indices; values of any sign. -/
theorem half_partition_of_le {n m : ℕ} (u : Fin n → Fin m → ℚ) (hmn : m ≤ n) :
    IsConsensusHalving u (fun _ => (1 / 2 : ℚ)) ∧
      numCuts (fun _ : Fin m => (1 / 2 : ℚ)) = min n m := by sorry

end ConsensusHalvingItems.Additive
