-- Prove2me | solution 1 for vojta_conjecture
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:22:01.566269+00:00
-- url     : https://prove2.me/submissions/eb76a647-8b0a-449a-91c8-daa9aab9e470

import Mathlib

theorem solution :
    ∀ (d : ℕ) (eps : ℝ) (_ : 0 < eps),
    ∃ C : ℝ, ∀ (x y : ℤ),
      Nat.Coprime x.natAbs y.natAbs →
      (∃ a b : ℤ, x ^ 2 + y ^ 2 = a * b ∧ a ≠ 0 ∧ b ≠ 0) →
      (x : ℝ) ^ 2 + (y : ℝ) ^ 2 ≤ C * max |x| |y| ^ (2 + eps) := by
  intro d eps heps
  refine ⟨2, fun x y hcop _ => ?_⟩
  have hne : ¬ (x = 0 ∧ y = 0) := by
    rintro ⟨rfl, rfl⟩
    simp [Nat.Coprime] at hcop
  set m : ℤ := max |x| |y| with hm
  have hm1 : (1 : ℤ) ≤ m := by
    rcases not_and_or.mp hne with hx | hy
    · exact le_trans (Int.one_le_abs hx) (le_max_left _ _)
    · exact le_trans (Int.one_le_abs hy) (le_max_right _ _)
  have hM1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
  have hxm : |x| ≤ m := le_max_left _ _
  have hym : |y| ≤ m := le_max_right _ _
  have hxM : (x : ℝ) ^ 2 ≤ (m : ℝ) ^ 2 := by
    have h1 : |(x : ℝ)| ≤ (m : ℝ) := by
      rw [← Int.cast_abs]; exact_mod_cast hxm
    calc (x : ℝ) ^ 2 = |(x : ℝ)| ^ 2 := (sq_abs _).symm
      _ ≤ (m : ℝ) ^ 2 := by gcongr
  have hyM : (y : ℝ) ^ 2 ≤ (m : ℝ) ^ 2 := by
    have h1 : |(y : ℝ)| ≤ (m : ℝ) := by
      rw [← Int.cast_abs]; exact_mod_cast hym
    calc (y : ℝ) ^ 2 = |(y : ℝ)| ^ 2 := (sq_abs _).symm
      _ ≤ (m : ℝ) ^ 2 := by gcongr
  have hpow : (m : ℝ) ^ (2 : ℝ) ≤ (m : ℝ) ^ (2 + eps) :=
    Real.rpow_le_rpow_of_exponent_le hM1 (by linarith)
  have h2 : (m : ℝ) ^ (2 : ℝ) = (m : ℝ) ^ 2 := by
    exact_mod_cast Real.rpow_natCast (m : ℝ) 2
  calc (x : ℝ) ^ 2 + (y : ℝ) ^ 2 ≤ (m : ℝ) ^ 2 + (m : ℝ) ^ 2 := add_le_add hxM hyM
    _ = 2 * (m : ℝ) ^ 2 := by ring
    _ = 2 * (m : ℝ) ^ (2 : ℝ) := by rw [h2]
    _ ≤ 2 * (m : ℝ) ^ (2 + eps) := by gcongr
