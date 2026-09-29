-- Prove2me | Theorems.Thm_BlockCycleRotation_exists_residue
-- name    : BlockCycleRotation.exists_residue
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:55:38.517274+00:00
-- url     : https://prove2.me/theorems/9db712bc-0b9e-4402-88e5-903a27cfa1aa
-- title:
--   With `gcd(a,a') = 1`, the congruence `a ∣ m - a'·b'` is `b' ≡ c (mod a)` for a residue `c` depending only on `a`, `a'` and `m`
-- statement:
--   With `gcd(a,a') = 1`, the congruence `a ∣ m - a'·b'` is `b' ≡ c (mod a)` for a residue `c` depending only on `a`, `a'` and `m`.
--
--   In Blomer–Bux this is **§4**, “Congruence → arithmetic progression”. It is used in the proofs of `inner_gt_sum_eq`, `inner_sum_nat_eq`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- §4. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/TripleSum.lean#L233-L256

import Mathlib

open Real Finset

theorem BlockCycleRotation.exists_residue {a a' m : ℕ} (hgcd : Nat.gcd a a' = 1) :
    ∃ c : ℤ, ∀ b : ℤ, ((a : ℤ) ∣ ((m : ℤ) - a' * b)) ↔ ((a : ℤ) ∣ (b - c)) := by sorry
