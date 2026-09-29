-- Prove2me | Theorems.Thm_BlockCycleRotation_sum_ap_eq
-- name    : BlockCycleRotation.sum_ap_eq
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:53:17.365995+00:00
-- url     : https://prove2.me/theorems/fc053769-b0d6-44c9-ac15-f6e1b47feaf8
-- title:
--   The character expansion of a sum over an arithmetic progression
-- statement:
--   **The character expansion of a sum over an arithmetic progression.** The `m = 0` term is the main term; the rest is the error.
--
--   This is an auxiliary lemma of the formalization rather than a result stated in the paper. It is used in the proof of `sum_ap_sub_main_le`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Progression.lean#L46-L75

import Definitions.Def_BlockCycleRotation_ExpSum
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.sum_ap_eq {a : ℕ} (ha : 0 < a) (c : ℤ) (A B : ℂ) (T : ℕ) :
    (∑ b ∈ Finset.Ico 1 T, if (a : ℤ) ∣ ((b : ℤ) - c) then (A + B * b) else 0)
      = (1 / (a : ℂ)) * ((∑ b ∈ Finset.Ico 1 T, (A + B * b))
          + ∑ m ∈ Finset.Ico 1 a, e (-(2 * π * (m : ℝ) * (c : ℝ) / a))
              * ∑ b ∈ Finset.Ico 1 T, (A + B * b) * e (2 * π * (m : ℝ) / a) ^ b) := by sorry
