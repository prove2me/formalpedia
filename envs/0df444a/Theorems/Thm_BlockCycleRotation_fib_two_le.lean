-- Prove2me | Theorems.Thm_BlockCycleRotation_fib_two_le
-- name    : BlockCycleRotation.fib_two_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:51:42.660085+00:00
-- url     : https://prove2.me/theorems/67fb9815-6c70-4819-9661-2fb63b93088e
-- title:
--   fib two le
-- statement:
--   A supporting lemma of the formalization, declared as `fib_two_le`.
--
--   This is an auxiliary lemma of the formalization rather than a result stated in the paper.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Algorithm.lean#L180-L183

import Mathlib

theorem BlockCycleRotation.fib_two_le {j : ℕ} : 2 ≤ Nat.fib (j + 3) := by sorry
