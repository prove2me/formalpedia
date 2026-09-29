-- Prove2me | Theorems.Thm_BlockCycleRotation_norm_sum_twisted_le
-- name    : BlockCycleRotation.norm_sum_twisted_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:53:24.738311+00:00
-- url     : https://prove2.me/theorems/c3b4eee5-7fce-473b-be81-06665148de84
-- title:
--   The error term of §4
-- statement:
--   **The error term of §4.** Summing the inner sums over the nontrivial characters, against arbitrary weights of modulus at most one, costs a harmonic sum — this is where the `log a` of Lemma 16 comes from.
--
--   In Blomer–Bux this is **Lemma 16**, “Error term over all `m ≠ 0`”. It is used in the proof of `sum_ap_sub_main_le`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Lemma 16. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/LinearSums.lean#L67-L117

import Definitions.Def_BlockCycleRotation_ExpSum
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.norm_sum_twisted_le {a : ℕ} (A B : ℂ) (T : ℕ) (w : ℕ → ℂ) (hw : ∀ m, ‖w m‖ ≤ 1) :
    ‖∑ m ∈ Finset.Ico 1 a, w m * ∑ b ∈ Finset.Ico 1 T,
        (A + B * b) * e (2 * π * (m : ℝ) / a) ^ b‖
      ≤ (‖A‖ + ‖B‖ * (T - 1 : ℕ)) * (a : ℝ) * ∑ m ∈ Finset.Ico 1 a, (1 : ℝ) / (m : ℝ) := by sorry
