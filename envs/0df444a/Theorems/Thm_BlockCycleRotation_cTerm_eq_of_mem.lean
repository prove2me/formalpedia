-- Prove2me | Theorems.Thm_BlockCycleRotation_cTerm_eq_of_mem
-- name    : BlockCycleRotation.cTerm_eq_of_mem
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:58:07.770042+00:00
-- url     : https://prove2.me/theorems/ad6a79f2-4bcf-44d3-aed8-fde9197bb945
-- title:
--   The value of `cTerm` on an admissible pair, in the paper's split form
-- statement:
--   The value of `cTerm` on an admissible pair, in the paper's split form.
--
--   This is an auxiliary lemma of the formalization rather than a result stated in the paper.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Constant.lean#L131-L146

import Definitions.Def_BlockCycleRotation_Constant
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.cTerm_eq_of_mem {a a' : ℕ} (h1 : 1 ≤ a') (h2 : a' < a) (h3 : Nat.gcd a a' = 1) :
    cTerm (a, a')
      = 1 / ((a : ℝ) ^ 2 * ((a : ℝ) + a')) - (a' : ℝ) / (2 * (a : ℝ) ^ 2 * ((a : ℝ) + a') ^ 2) := by sorry
