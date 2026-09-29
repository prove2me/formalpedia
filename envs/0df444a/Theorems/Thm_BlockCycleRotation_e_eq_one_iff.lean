-- Prove2me | Theorems.Thm_BlockCycleRotation_e_eq_one_iff
-- name    : BlockCycleRotation.e_eq_one_iff
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:52:59.178617+00:00
-- url     : https://prove2.me/theorems/8583cbda-502f-491a-9864-49459c2ddbe1
-- title:
--   `e θ = 1` exactly on the integer multiples of `2π`
-- statement:
--   `e θ = 1` exactly on the integer multiples of `2π`.
--
--   This is an auxiliary lemma of the formalization rather than a result stated in the paper. It is used in the proof of `sum_e_root`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Orthogonality.lean#L29-L40

import Definitions.Def_BlockCycleRotation_ExpSum
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.e_eq_one_iff (θ : ℝ) : e θ = 1 ↔ ∃ n : ℤ, θ = 2 * π * n := by sorry
