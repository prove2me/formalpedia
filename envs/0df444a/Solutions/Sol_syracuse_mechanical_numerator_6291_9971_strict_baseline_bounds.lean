-- Prove2me | solution 1 for syracuse_mechanical_numerator_6291_9971_strict_baseline_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T02:33:22.58987+00:00
-- url     : https://prove2.me/submissions/5e67e1b7-cc46-4084-9654-6621f1460052

import Mathlib

set_option autoImplicit false

open scoped BigOperators

theorem ab3539bc_sum_eq_rec (g : ℕ → ℕ) (n : ℕ) :
    (∑ j ∈ Finset.range n, g j) = Nat.rec (motive := fun _ => ℕ) 0 (fun k acc => acc + g k) n := by
  induction n with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]

theorem ab3539bc_lower :
    2403660 * ((2 : ℕ) ^ 9971 - 3 ^ 6291) <
      Nat.rec (motive := fun _ => ℕ) 0
        (fun k acc => acc + (3 : ℕ) ^ (6291 - 1 - k) * 2 ^ ((9971 * k) / 6291)) 6291 := by
  decide +kernel

theorem ab3539bc_upper :
    Nat.rec (motive := fun _ => ℕ) 0
        (fun k acc => acc + (3 : ℕ) ^ (6291 - 1 - k) * 2 ^ ((9971 * k) / 6291)) 6291 <
      2403661 * ((2 : ℕ) ^ 9971 - 3 ^ 6291) := by
  decide +kernel

theorem ab3539bc_gap : (3 : ℕ) ^ 6291 < 2 ^ 9971 := by
  decide +kernel

theorem solution :
    (3 : ℕ) ^ 6291 < 2 ^ 9971 ∧
      2403660 * ((2 : ℕ) ^ 9971 - 3 ^ 6291) <
        (∑ j ∈ Finset.range 6291,
          (3 : ℕ) ^ (6291 - 1 - j) * 2 ^ ((9971 * j) / 6291)) ∧
      (∑ j ∈ Finset.range 6291,
        (3 : ℕ) ^ (6291 - 1 - j) * 2 ^ ((9971 * j) / 6291)) <
        2403661 * ((2 : ℕ) ^ 9971 - 3 ^ 6291) := by
  rw [ab3539bc_sum_eq_rec (fun j => (3 : ℕ) ^ (6291 - 1 - j) * 2 ^ ((9971 * j) / 6291)) 6291]
  exact ⟨ab3539bc_gap, ab3539bc_lower, ab3539bc_upper⟩
