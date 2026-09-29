-- Prove2me | Theorems.Thm_BlockCycleRotation_card_mod_filter_le
-- name    : BlockCycleRotation.card_mod_filter_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:57:15.420269+00:00
-- url     : https://prove2.me/theorems/7fa807e5-c477-4c4a-90f6-1c7c5783e366
-- title:
--   Counting a residue class in an interval
-- statement:
--   **Counting a residue class in an interval.**
--
--   In Blomer–Bux this is **Lemma 19**, “AP counting `≤ U/a + 1`”. It is used in the proof of `card_dvd_filter_le`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Lemma 19. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/TripleSum.lean#L1235-L1257

import Mathlib

open Real Finset

theorem BlockCycleRotation.card_mod_filter_le {a U c : ℕ} (ha : 0 < a) :
    (((Finset.Ico 1 U).filter (fun b => b % a = c)).card) ≤ U / a + 1 := by sorry
