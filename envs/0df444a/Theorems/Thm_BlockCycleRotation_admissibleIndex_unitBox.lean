-- Prove2me | Theorems.Thm_BlockCycleRotation_admissibleIndex_unitBox
-- name    : BlockCycleRotation.admissibleIndex_unitBox
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:04:17.861606+00:00
-- url     : https://prove2.me/theorems/be72b7e0-e74f-48f1-9714-87e642b8d2ef
-- title:
--   The boxes of the uniform subdivision of `[0,1]` are indexed by `0,…,n-1`
-- statement:
--   The boxes of the uniform subdivision of `[0,1]` are indexed by `0,…,n-1`.
--
--   This is an auxiliary lemma of the formalization rather than a result stated in the paper. It is used in the proof of `integralSum_prepartition`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Theorem10.lean#L804-L834

import Definitions.Def_BlockCycleRotation_Theorem10
import Mathlib

open BlockCycleRotation
open Finset Real Filter Topology MeasureTheory BoxIntegral
open scoped ENNReal

theorem BlockCycleRotation.admissibleIndex_unitBox (n : ℕ) [NeZero n] :
    unitPartition.admissibleIndex n unitBox
      = (Finset.range n).image (fun j : ℕ => (fun _ : Fin 1 => (j : ℤ))) := by sorry
