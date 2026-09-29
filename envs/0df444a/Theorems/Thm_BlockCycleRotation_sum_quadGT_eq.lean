-- Prove2me | Theorems.Thm_BlockCycleRotation_sum_quadGT_eq
-- name    : BlockCycleRotation.sum_quadGT_eq
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:56:26.186217+00:00
-- url     : https://prove2.me/theorems/bfbe63f1-7871-4fb2-8b79-be105f6d12b9
-- title:
--   The `b`-elimination on the restricted set
-- statement:
--   **The `b`-elimination on the restricted set.**
--
--   This is an auxiliary lemma of the formalization rather than a result stated in the paper. It is used in the proof of `Q_gt_tripleSum`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/TripleSum.lean#L698-L745

import Definitions.Def_BlockCycleRotation_TripleSum
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.sum_quadGT_eq {m d : ℕ} (hm : 0 < m) :
    ∑ q ∈ quadGT m d, (d * q.1 + q.2.1)
      = ∑ t ∈ gtTriples m d, (d * t.1 + (m - t.2.1 * t.2.2) / t.1) := by sorry
