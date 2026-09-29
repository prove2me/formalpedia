-- Prove2me | solution 1 for gcd_cyclotomic_dvd_19
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-12T07:30:46.662375+00:00
-- url     : https://prove2.me/submissions/daebe6cc-0419-4c81-ac25-ba812bbc14eb

import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.Ring

-- Q19 = sum_{k=0}^{17} (-1)^k*(k+1)*a^(17-k)*b^k  (18 terms, degree 17)
-- Key: 19*b^18 = Phi19(a,b) - (a+b)*Q19(a,b)

theorem solution (a b : ℤ) (hab : Int.gcd a b = 1) :
    (Int.gcd (a + b) (a ^ 18 - a ^ 17 * b + a ^ 16 * b ^ 2 - a ^ 15 * b ^ 3 + a ^ 14 * b ^ 4 -
      a ^ 13 * b ^ 5 + a ^ 12 * b ^ 6 - a ^ 11 * b ^ 7 + a ^ 10 * b ^ 8 - a ^ 9 * b ^ 9 +
      a ^ 8 * b ^ 10 - a ^ 7 * b ^ 11 + a ^ 6 * b ^ 12 - a ^ 5 * b ^ 13 + a ^ 4 * b ^ 14 -
      a ^ 3 * b ^ 15 + a ^ 2 * b ^ 16 - a * b ^ 17 + b ^ 18) : ℤ) ∣ 19 := by
  set D := Int.gcd (a + b) (a ^ 18 - a ^ 17 * b + a ^ 16 * b ^ 2 - a ^ 15 * b ^ 3 +
      a ^ 14 * b ^ 4 - a ^ 13 * b ^ 5 + a ^ 12 * b ^ 6 - a ^ 11 * b ^ 7 + a ^ 10 * b ^ 8 -
      a ^ 9 * b ^ 9 + a ^ 8 * b ^ 10 - a ^ 7 * b ^ 11 + a ^ 6 * b ^ 12 - a ^ 5 * b ^ 13 +
      a ^ 4 * b ^ 14 - a ^ 3 * b ^ 15 + a ^ 2 * b ^ 16 - a * b ^ 17 + b ^ 18)
  have hD_ab  : (D : ℤ) ∣ (a + b) := Int.gcd_dvd_left _ _
  have hD_phi : (D : ℤ) ∣ (a ^ 18 - a ^ 17 * b + a ^ 16 * b ^ 2 - a ^ 15 * b ^ 3 +
      a ^ 14 * b ^ 4 - a ^ 13 * b ^ 5 + a ^ 12 * b ^ 6 - a ^ 11 * b ^ 7 + a ^ 10 * b ^ 8 -
      a ^ 9 * b ^ 9 + a ^ 8 * b ^ 10 - a ^ 7 * b ^ 11 + a ^ 6 * b ^ 12 - a ^ 5 * b ^ 13 +
      a ^ 4 * b ^ 14 - a ^ 3 * b ^ 15 + a ^ 2 * b ^ 16 - a * b ^ 17 + b ^ 18) :=
    Int.gcd_dvd_right _ _
  have hD_19b18 : (D : ℤ) ∣ 19 * b ^ 18 := by
    obtain ⟨s, hs⟩ := hD_phi
    obtain ⟨t, ht⟩ := hD_ab
    exact ⟨s - t * (a ^ 17 - 2 * a ^ 16 * b + 3 * a ^ 15 * b ^ 2 - 4 * a ^ 14 * b ^ 3 +
        5 * a ^ 13 * b ^ 4 - 6 * a ^ 12 * b ^ 5 + 7 * a ^ 11 * b ^ 6 - 8 * a ^ 10 * b ^ 7 +
        9 * a ^ 9 * b ^ 8 - 10 * a ^ 8 * b ^ 9 + 11 * a ^ 7 * b ^ 10 - 12 * a ^ 6 * b ^ 11 +
        13 * a ^ 5 * b ^ 12 - 14 * a ^ 4 * b ^ 13 + 15 * a ^ 3 * b ^ 14 - 16 * a ^ 2 * b ^ 15 +
        17 * a * b ^ 16 - 18 * b ^ 17), by
      have key : 19 * b ^ 18 =
          (a ^ 18 - a ^ 17 * b + a ^ 16 * b ^ 2 - a ^ 15 * b ^ 3 + a ^ 14 * b ^ 4 -
          a ^ 13 * b ^ 5 + a ^ 12 * b ^ 6 - a ^ 11 * b ^ 7 + a ^ 10 * b ^ 8 - a ^ 9 * b ^ 9 +
          a ^ 8 * b ^ 10 - a ^ 7 * b ^ 11 + a ^ 6 * b ^ 12 - a ^ 5 * b ^ 13 + a ^ 4 * b ^ 14 -
          a ^ 3 * b ^ 15 + a ^ 2 * b ^ 16 - a * b ^ 17 + b ^ 18) -
          (a + b) * (a ^ 17 - 2 * a ^ 16 * b + 3 * a ^ 15 * b ^ 2 - 4 * a ^ 14 * b ^ 3 +
          5 * a ^ 13 * b ^ 4 - 6 * a ^ 12 * b ^ 5 + 7 * a ^ 11 * b ^ 6 - 8 * a ^ 10 * b ^ 7 +
          9 * a ^ 9 * b ^ 8 - 10 * a ^ 8 * b ^ 9 + 11 * a ^ 7 * b ^ 10 - 12 * a ^ 6 * b ^ 11 +
          13 * a ^ 5 * b ^ 12 - 14 * a ^ 4 * b ^ 13 + 15 * a ^ 3 * b ^ 14 - 16 * a ^ 2 * b ^ 15 +
          17 * a * b ^ 16 - 18 * b ^ 17) := by ring
      rw [key, hs, ht]; ring⟩
  have hD_dvd_ab_nat : D ∣ (a + b).natAbs := by
    exact_mod_cast Int.natAbs_dvd_natAbs.mpr hD_ab
  have hgcd_ab_b : Int.gcd (a + b) b = 1 := by
    rw [Int.gcd_comm]
    have h := @Int.gcd_add_mul_right_right b a 1
    simp only [one_mul] at h
    rw [h, Int.gcd_comm]; exact hab
  have hcop_D_b : Nat.Coprime D b.natAbs := by
    unfold Nat.Coprime; apply Nat.eq_one_of_dvd_one
    have h1 := Nat.gcd_dvd_left D b.natAbs
    have h2 := Nat.gcd_dvd_right D b.natAbs
    have h3 : Nat.gcd D b.natAbs ∣ (a + b).natAbs := dvd_trans h1 hD_dvd_ab_nat
    have h4 := Nat.dvd_gcd h3 h2
    rwa [show Nat.gcd (a + b).natAbs b.natAbs = 1 from hgcd_ab_b] at h4
  have hcop_D_b18 : Nat.Coprime D (b ^ 18).natAbs := by
    rw [Int.natAbs_pow]; exact hcop_D_b.pow_right 18
  have hD_dvd_19b18_nat : D ∣ 19 * (b ^ 18).natAbs := by
    have h := Int.natAbs_dvd_natAbs.mpr hD_19b18
    rw [Int.natAbs_mul] at h; norm_cast at h
  exact_mod_cast hcop_D_b18.dvd_of_dvd_mul_right hD_dvd_19b18_nat
