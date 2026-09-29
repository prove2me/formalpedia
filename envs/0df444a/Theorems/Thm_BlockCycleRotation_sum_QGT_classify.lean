-- Prove2me | Theorems.Thm_BlockCycleRotation_sum_QGT_classify
-- name    : BlockCycleRotation.sum_QGT_classify
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:56:35.236428+00:00
-- url     : https://prove2.me/theorems/9a6f37c7-bc2c-40c6-ab06-e7f62177d565
-- title:
--   The symmetrised sum, classified by `gcd(a,a')`
-- statement:
--   **The symmetrised sum, classified by `gcd(a,a')`.**
--
--   In Blomer–Bux this is **§4**, “`b > a` through the classification”. It is used in the proof of `Q_gt_tripleSum`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- §4. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/TripleSum.lean#L610-L684

import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_TripleSum
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.sum_QGT_classify {n : ℕ} (hn : 0 < n) :
    ∑ q ∈ (quadruplesQ n).filter (fun q => q.1 < q.2.1), (q.1 + q.2.1)
      = ∑ d ∈ n.divisors, ∑ q ∈ quadGT (n / d) d, (d * q.1 + q.2.1) := by sorry
