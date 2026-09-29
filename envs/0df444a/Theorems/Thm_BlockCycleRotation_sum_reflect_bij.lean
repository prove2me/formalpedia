-- Prove2me | Theorems.Thm_BlockCycleRotation_sum_reflect_bij
-- name    : BlockCycleRotation.sum_reflect_bij
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:03:10.668818+00:00
-- url     : https://prove2.me/theorems/e52fd2af-1d26-468c-912d-a012980a5b22
-- title:
--   The reflection is a bijection between the upper-half shifts and the strictly-lower-half ones
-- statement:
--   The reflection is a bijection between the upper-half shifts and the strictly-lower-half ones.
--
--   This is an auxiliary lemma of the formalization rather than a result stated in the paper.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/AllShifts.lean#L76-L96

import Definitions.Def_BlockCycleRotation_AllShifts
import Definitions.Def_BlockCycleRotation_Euclid
import Mathlib

open BlockCycleRotation
open Filter Topology Finset Real

theorem BlockCycleRotation.sum_reflect_bij {n : ℕ} :
    ∑ k ∈ bigShifts n, remSum n (n - k) = ∑ j ∈ smallShifts n, remSum n j := by sorry
