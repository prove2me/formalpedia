-- Prove2me | Theorems.Thm_BlockCycleRotation_bulk_empty_of_small
-- name    : BlockCycleRotation.bulk_empty_of_small
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:59:02.108214+00:00
-- url     : https://prove2.me/theorems/b579edec-3045-4282-a36f-194734fae6a4
-- title:
--   The bulk set is empty when `m` is small relative to `d`
-- statement:
--   **The bulk set is empty when `m` is small relative to `d`.**
--
--   This is an auxiliary lemma of the formalization rather than a result stated in the paper. It is used in the proof of `lemma17_E`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Constant.lean#L558-L571

import Definitions.Def_BlockCycleRotation_TripleSum
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.bulk_empty_of_small {m d : ℕ} (h : m < 6 * d) :
    (coprimePairs m).filter (fun p => d * p.1 * (p.1 + p.2) ≤ m) = ∅ := by sorry
