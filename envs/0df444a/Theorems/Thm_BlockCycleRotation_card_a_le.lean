-- Prove2me | Theorems.Thm_BlockCycleRotation_card_a_le
-- name    : BlockCycleRotation.card_a_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:56:49.127562+00:00
-- url     : https://prove2.me/theorems/c1aabc61-63d4-4a44-b6ea-405531c6bfaa
-- title:
--   The admissible `a` are at most `√((m-1)/d)`
-- statement:
--   The admissible `a` are at most `√((m-1)/d)`.
--
--   In Blomer–Bux this is **§4**, “Admissible `a` number `≤ √((m−1)/d)`”. It is used in the proofs of `lower_order_le`, `middle_layer`, `small_part_le`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- §4. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/TripleSum.lean#L979-L994

import Mathlib

open Real Finset

theorem BlockCycleRotation.card_a_le {m d : ℕ} (hd : 0 < d) :
    ((Finset.range (m + 1)).filter (fun a => d * a * a < m)).card
      ≤ Nat.sqrt ((m - 1) / d) + 1 := by sorry
