-- Prove2me | Theorems.Thm_BlockCycleRotation_algCost_add_gcd_le
-- name    : BlockCycleRotation.algCost_add_gcd_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T11:51:09.188689+00:00
-- url     : https://prove2.me/theorems/b0c3ab67-02f0-4138-83c3-e4751687cfde
-- title:
--   Observation 2: at most $3(n-\gcd(n,k))$ moves, for any shift
-- statement:
--   Let $k \le n$ and let $\operatorname{algCost}(n,k)$ be the number of moves the block cycle algorithm performs rotating an array of length $n$ by $k$, recursing on the shorter segment. Then
--   $$\operatorname{algCost}(n,k) + 3\gcd(n,k) \le 3n,$$
--   that is, at most $3(n - \gcd(n,k))$ moves.
--
--   This is **Observation 2** at the paper's generality: the paper states the bound with no restriction on $k$, whereas the arithmetic core `moveCount_add_gcd_le` assumes $2k \le n$. The two are bridged by `gcd_min_eq`, since the algorithm reflects a large shift to $\min(k, n-k)$ and the $\gcd$ is unaffected. It is the sharp form of the $3n$ worst-case half of Theorem A.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Observation 2. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Average.lean#L38-L44

import Definitions.Def_BlockCycleRotation_Average
import Mathlib

open BlockCycleRotation
open Finset

theorem BlockCycleRotation.algCost_add_gcd_le {n k : ℕ} (h : k ≤ n) :
    algCost n k + 3 * Nat.gcd n k ≤ 3 * n := by sorry
