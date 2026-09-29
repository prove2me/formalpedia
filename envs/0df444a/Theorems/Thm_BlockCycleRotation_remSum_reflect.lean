-- Prove2me | Theorems.Thm_BlockCycleRotation_remSum_reflect
-- name    : BlockCycleRotation.remSum_reflect
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:02:49.872697+00:00
-- url     : https://prove2.me/theorems/18e9a89c-7f53-417d-937d-d272d102f886
-- title:
--   Reflection: $\operatorname{remSum}(n,k) = k + \operatorname{remSum}(n,n-k)$
-- statement:
--   For $k \le n < 2k$,
--   $$\operatorname{remSum}(n,k) = k + \operatorname{remSum}(n, n-k).$$
--
--   When the shift exceeds half the array the first Euclidean step contributes the remainder $n-k$ and then repeats the run on $(n,n-k)$. This is the reflection used in the remark on all shifts: it reduces an average over $1 \le k \le n$ to the average over $2k \le n$ that the main theorems control, at the cost of the explicit term $\sum_{k>n/2} k = \tfrac{3}{8}n^2 + O(n)$.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Remark 20. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/AllShifts.lean#L47-L60

import Definitions.Def_BlockCycleRotation_Euclid
import Mathlib

open BlockCycleRotation
open Filter Topology Finset Real

theorem BlockCycleRotation.remSum_reflect {n k : ℕ} (hk : k ≤ n) (h : n < 2 * k) :
    remSum n k = k + remSum n (n - k) := by sorry
