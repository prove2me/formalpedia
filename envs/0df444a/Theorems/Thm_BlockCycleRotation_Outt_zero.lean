-- Prove2me | Theorems.Thm_BlockCycleRotation_Outt_zero
-- name    : BlockCycleRotation.Outt_zero
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:03:27.677886+00:00
-- url     : https://prove2.me/theorems/aa120312-2337-4eec-b083-084ca95fd2ba
-- title:
--   Outt zero
-- statement:
--   A supporting lemma of the formalization, declared as `Outt_zero`.
--
--   This is an auxiliary lemma of the formalization rather than a result stated in the paper.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Theorem10.lean#L48-L48

import Definitions.Def_BlockCycleRotation_Theorem10
import Mathlib

open BlockCycleRotation
open Finset Real Filter Topology MeasureTheory BoxIntegral
open scoped ENNReal

theorem BlockCycleRotation.Outt_zero : Outt 0 = 0 := by sorry
