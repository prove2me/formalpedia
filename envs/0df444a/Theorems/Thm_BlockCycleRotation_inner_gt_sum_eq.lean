-- Prove2me | Theorems.Thm_BlockCycleRotation_inner_gt_sum_eq
-- name    : BlockCycleRotation.inner_gt_sum_eq
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:56:38.104603+00:00
-- url     : https://prove2.me/theorems/d10d924b-b2c4-452f-97a9-b0deefe8abd6
-- title:
--   The inner sum of the restricted triple sum, as an arithmetic-progression sum with the paper's coefficients `A = d·a + m/a` and `B = -a'/a`
-- statement:
--   The inner sum of the restricted triple sum, as an arithmetic-progression sum with the paper's coefficients `A = d·a + m/a` and `B = -a'/a`.
--
--   This is an auxiliary lemma of the formalization rather than a result stated in the paper. It is used in the proof of `inner_gt_estimate`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/TripleSum.lean#L882-L918

import Mathlib

open Real Finset

theorem BlockCycleRotation.inner_gt_sum_eq {m d a a' : ℕ} (ha : 0 < a) (hgcd : Nat.gcd a a' = 1) :
    ∃ c : ℤ, ∀ U : ℕ, (∀ b' ∈ Finset.Ico 1 U, a' * b' ≤ m) →
      ((∑ b' ∈ (Finset.Ico 1 U).filter (fun b' => a ∣ (m - a' * b')),
          (d * a + (m - a' * b') / a) : ℕ) : ℝ)
        = ∑ b' ∈ Finset.Ico 1 U,
            (if (a : ℤ) ∣ ((b' : ℤ) - c) then
              ((((d * a : ℕ) : ℝ) + (m : ℝ) / a) + (-(a' : ℝ) / a) * b') else 0) := by sorry
