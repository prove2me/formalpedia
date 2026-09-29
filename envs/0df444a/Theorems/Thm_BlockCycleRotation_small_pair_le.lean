-- Prove2me | Theorems.Thm_BlockCycleRotation_small_pair_le
-- name    : BlockCycleRotation.small_pair_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:57:31.768386+00:00
-- url     : https://prove2.me/theorems/79d2841b-8a32-4eb4-b1f7-4c5453c09f00
-- title:
--   The per-pair bound on the small branch
-- statement:
--   **The per-pair bound on the small branch.**
--
--   This is an auxiliary lemma of the formalization rather than a result stated in the paper. It is used in the proof of `small_part_le`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/TripleSum.lean#L1300-L1352

import Definitions.Def_BlockCycleRotation_TripleSum
import Mathlib

open BlockCycleRotation
open Real Finset

theorem BlockCycleRotation.small_pair_le {m d a a' : ℕ} (ha : 0 < a) (ha' : 0 < a') (hgcd : Nat.gcd a a' = 1)
    (hda : d * a * a < m) (haa : a' < a) (hsmall : ¬ (d * a * (a + a') ≤ m)) :
    ∑ b' ∈ (Finset.Ico 1 (gtBound m d a a')).filter (fun b' => a ∣ (m - a' * b')),
        (d * a + (m - a' * b') / a)
      ≤ (2 * d + 2) * (2 * (m / a)) := by sorry
