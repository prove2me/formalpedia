-- Prove2me | Theorems.Thm_BlockCycleRotation_sum_e_root
-- name    : BlockCycleRotation.sum_e_root
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:52:44.383619+00:00
-- url     : https://prove2.me/theorems/ad29e7c1-fe15-4762-a901-66c94f547f97
-- title:
--   Orthogonality
-- statement:
--   **Orthogonality.** `∑_{m < a} e(2πmr/a)` is `a` when `a ∣ r` and `0` otherwise.
--
--   In Blomer–Bux this is **§4**, “Character orthogonality”. It is used in the proof of `indicator_eq`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- §4. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Orthogonality.lean#L42-L80

import Definitions.Def_BlockCycleRotation_ExpSum
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.sum_e_root {a : ℕ} (ha : 0 < a) (r : ℤ) :
    ∑ _m ∈ Finset.range a, (e (2 * π * r / a)) ^ _m
      = if (a : ℤ) ∣ r then (a : ℂ) else 0 := by sorry
