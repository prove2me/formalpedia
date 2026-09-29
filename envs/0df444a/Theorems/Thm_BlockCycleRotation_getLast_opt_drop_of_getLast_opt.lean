-- Prove2me | Theorems.Thm_BlockCycleRotation_getLast_opt_drop_of_getLast_opt
-- name    : BlockCycleRotation.getLast_opt_drop_of_getLast_opt
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:54:24.945449+00:00
-- url     : https://prove2.me/theorems/c8546cff-98ef-4d26-9894-327ca3e62453
-- title:
--   A suffix inherits the last-entry condition
-- statement:
--   A suffix inherits the last-entry condition.
--
--   This is an auxiliary lemma of the formalization rather than a result stated in the paper. It is used in the proof of `split_quadruple`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Continuant.lean#L612-L624

import Mathlib

open Real Finset

theorem BlockCycleRotation.getLast_opt_drop_of_getLast_opt {L : List ℕ} {j : ℕ} (hj : j < L.length)
    (hlast : ∀ x ∈ L.getLast?, 2 ≤ x) : ∀ x ∈ (L.drop j).getLast?, 2 ≤ x := by sorry
