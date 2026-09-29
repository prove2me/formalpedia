-- Prove2me | Theorems.Thm_BlockCycleRotation_card_dvd_filter_le
-- name    : BlockCycleRotation.card_dvd_filter_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:57:12.849101+00:00
-- url     : https://prove2.me/theorems/eef6c370-e688-442d-9bb8-d8394b523268
-- title:
--   The divisibility condition confines `b'` to one residue class
-- statement:
--   **The divisibility condition confines `b'` to one residue class.**
--
--   This is an auxiliary lemma of the formalization rather than a result stated in the paper. It is used in the proof of `small_pair_le`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/TripleSum.lean#L1259-L1291

import Mathlib

open Real Finset

theorem BlockCycleRotation.card_dvd_filter_le {m a a' U : ℕ} (ha : 0 < a) (hgcd : Nat.gcd a a' = 1)
    (hU : ∀ b ∈ Finset.Ico 1 U, a' * b ≤ m) :
    (((Finset.Ico 1 U).filter (fun b => a ∣ (m - a' * b))).card) ≤ U / a + 1 := by sorry
