-- Prove2me | Theorems.Thm_BlockCycleRotation_inner_sum_nat_eq
-- name    : BlockCycleRotation.inner_sum_nat_eq
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:55:40.556178+00:00
-- url     : https://prove2.me/theorems/174e3533-3ed8-44b4-8ecb-9e9cd4987b3c
-- title:
--   The inner sum of the triple sum, as an arithmetic-progression sum
-- statement:
--   **The inner sum of the triple sum, as an arithmetic-progression sum.** The natural-number inner sum `∑ (m - a'b')/a`, taken over `b'` satisfying the divisibility condition, is the real sum of the linear function `m/a - (a'/a)·b'` over an arithmetic progression modulo `a` — the exact shape `sum_ap_sub_main_le_log` estimates.
--
--   In Blomer–Bux this is **§4**, “Inner sum as an AP sum”.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- §4. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/TripleSum.lean#L258-L297

import Mathlib

open Real Finset

theorem BlockCycleRotation.inner_sum_nat_eq {m a a' : ℕ} (ha : 0 < a) (hgcd : Nat.gcd a a' = 1) :
    ∃ c : ℤ, ∀ U : ℕ, (∀ b' ∈ Finset.Ico 1 U, a' * b' ≤ m) →
      ((∑ b' ∈ (Finset.Ico 1 U).filter (fun b' => a ∣ (m - a' * b')),
          (m - a' * b') / a : ℕ) : ℝ)
        = ∑ b' ∈ Finset.Ico 1 U,
            (if (a : ℤ) ∣ ((b' : ℤ) - c) then ((m : ℝ) / a - (a' : ℝ) / a * b') else 0) := by sorry
