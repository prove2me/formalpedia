-- Prove2me | Theorems.Thm_BlockCycleRotation_sum_gt_eq_sum_lt
-- name    : BlockCycleRotation.sum_gt_eq_sum_lt
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:56:15.598586+00:00
-- url     : https://prove2.me/theorems/38147236-0333-43b3-a22b-e72a067e74f2
-- title:
--   The involution matches the quadruples with `b < a` against those with `b > a`
-- statement:
--   The involution matches the quadruples with `b < a` against those with `b > a`.
--
--   This is an auxiliary lemma of the formalization rather than a result stated in the paper. It is used in the proof of `Q_symmetrise`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/TripleSum.lean#L405-L423

import Definitions.Def_BlockCycleRotation_Continuant
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.sum_gt_eq_sum_lt (n : ℕ) :
    ∑ q ∈ (quadruplesQ n).filter (fun q => q.2.1 < q.1), (q.1 + q.2.1)
      = ∑ q ∈ (quadruplesQ n).filter (fun q => q.1 < q.2.1), (q.1 + q.2.1) := by sorry
