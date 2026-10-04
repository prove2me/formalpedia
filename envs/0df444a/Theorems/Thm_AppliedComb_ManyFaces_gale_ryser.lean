-- Prove2me | Theorems.Thm_AppliedComb_ManyFaces_gale_ryser
-- name    : AppliedComb.ManyFaces.gale_ryser
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T01:52:47.464969+00:00
-- url     : https://prove2.me/theorems/703ad6b8-fae7-4e5d-b7a3-b9a326e5c18d
-- title:
--   Theorem 16.12 — the Gale–Ryser Theorem
-- statement:
--   Let $t$ be a positive integer and let $R = (r_1, \dots, r_m)$ and $C = (c_1, \dots, c_n)$ be partitions of $t$ (non-increasing strings of positive integers summing to $t$). Let $R^d$ be the dual (conjugate) partition of $R$, whose $j$-th entry is the number of rows $i$ with $r_i \ge j$. Then there is an $m \times n$ zero–one matrix with row sum string $R$ and column sum string $C$ if and only if $R^d \ge C$ in the partial order on $\mathcal P(t)$:
--   $$\exists\, M \in \{0,1\}^{m \times n}:\ \text{row sums } R,\ \text{column sums } C \iff r_1 \le n \ \text{ and } \ \sum_{i \le j} (R^d)_i \ge \sum_{i \le j} c_i \ \text{ for } j = 1, \dots, r_1.$$
--
--   The theorem characterises the degree sequences of bipartite graphs with prescribed part sizes, and it is the basic existence result for zero–one matrices with prescribed margins.
--
--   **Formalization Note.** Partitions are lists satisfying `IsPartition t`, the order is `Dominates`, the dual is `dual`, and a matrix is `M : Matrix (Fin R.length) (Fin C.length) ℕ` satisfying `IsZeroOneMatrixWithSums R C M`. The page defines the dual partition with the misprinted rule "at least $n+1-j$", which gives an increasing string, and its worked example does not sum to $t$. The formalization uses the conjugate partition in non-increasing order, the only reading under which the theorem is true; see the definition `dualPartition`.
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), p. 325, Theorem 16.12

import Mathlib
import Definitions.Def_AppliedComb_ManyFaces_partitionDominance
import Definitions.Def_AppliedComb_ManyFaces_dualPartition
import Definitions.Def_AppliedComb_ManyFaces_zeroOneMatrix

namespace AppliedComb.ManyFaces

/-- Theorem 16.12 (Gale–Ryser; Keller & Trotter, *Applied Combinatorics* (2017 Edition), p. 325).
Let `R` and `C` be partitions of a positive integer `t`. Then there is a zero–one matrix with row
sum string `R` and column sum string `C` if and only if `R^d ≥ C` in the poset `P(t)`, where `R^d`
is the dual (conjugate) partition of `R`. -/
theorem gale_ryser (t : ℕ) (ht : 0 < t) (R C : List ℕ) (hR : IsPartition t R)
    (hC : IsPartition t C) :
    (∃ M : Matrix (Fin R.length) (Fin C.length) ℕ, IsZeroOneMatrixWithSums R C M) ↔
      Dominates (dual R) C := by sorry

end AppliedComb.ManyFaces
