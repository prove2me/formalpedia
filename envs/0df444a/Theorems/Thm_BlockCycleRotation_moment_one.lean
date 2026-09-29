-- Prove2me | Theorems.Thm_BlockCycleRotation_moment_one
-- name    : BlockCycleRotation.moment_one
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:05:13.800281+00:00
-- url     : https://prove2.me/theorems/859d91d7-4ec2-4fbc-b865-ae9f21b9ffeb
-- title:
--   The first moment is the constant of Theorem 9
-- statement:
--   The first moment is the constant of Theorem 9.
--
--   This is an auxiliary lemma of the formalization rather than a result stated in the paper.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Theorem10.lean#L1165-L1168

import Definitions.Def_BlockCycleRotation_Theorem10
import Mathlib

open BlockCycleRotation
open Finset Real Filter Topology MeasureTheory BoxIntegral
open scoped ENNReal

theorem BlockCycleRotation.moment_one : ∫ x, fCost x ^ 1 ∂unifHalf = 2 * ∫ x in (0 : ℝ)..(1 / 2), fCost x := by sorry
