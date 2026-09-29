-- Prove2me | Theorems.Thm_BlockCycleRotation_indicator_eq
-- name    : BlockCycleRotation.indicator_eq
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:53:05.760817+00:00
-- url     : https://prove2.me/theorems/c27c086f-0aca-4ad3-b3ef-6f625ef6981a
-- title:
--   The character expansion of the indicator of `b ≡ c mod a`
-- statement:
--   The character expansion of the indicator of `b ≡ c mod a`.
--
--   In Blomer–Bux this is **§4**, “Indicator via characters”. It is used in the proof of `sum_ap_eq`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- §4. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Progression.lean#L23-L44

import Definitions.Def_BlockCycleRotation_ExpSum
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.indicator_eq {a : ℕ} (ha : 0 < a) (c : ℤ) (b : ℕ) :
    (if (a : ℤ) ∣ ((b : ℤ) - c) then (1 : ℂ) else 0)
      = (1 / (a : ℂ)) * ∑ m ∈ Finset.range a,
          e (2 * π * (m : ℝ) / a) ^ b * e (-(2 * π * (m : ℝ) * (c : ℝ) / a)) := by sorry
