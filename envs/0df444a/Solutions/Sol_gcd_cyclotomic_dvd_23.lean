-- Prove2me | solution 1 for gcd_cyclotomic_dvd_23
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-12T07:30:47.022418+00:00
-- url     : https://prove2.me/submissions/1dcd0dee-38d7-47dd-b996-4cc13a412808

import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.Ring

-- Q23 = sum_{k=0}^{21} (-1)^k*(k+1)*a^(21-k)*b^k  (22 terms, degree 21)
-- Key: 23*b^22 = Phi23(a,b) - (a+b)*Q23(a,b)

theorem solution (a b : ℤ) (hab : Int.gcd a b = 1) :
    (Int.gcd (a + b) (a ^ 22 - a ^ 21 * b + a ^ 20 * b ^ 2 - a ^ 19 * b ^ 3 + a ^ 18 * b ^ 4 -
      a ^ 17 * b ^ 5 + a ^ 16 * b ^ 6 - a ^ 15 * b ^ 7 + a ^ 14 * b ^ 8 - a ^ 13 * b ^ 9 +
      a ^ 12 * b ^ 10 - a ^ 11 * b ^ 11 + a ^ 10 * b ^ 12 - a ^ 9 * b ^ 13 + a ^ 8 * b ^ 14 -
      a ^ 7 * b ^ 15 + a ^ 6 * b ^ 16 - a ^ 5 * b ^ 17 + a ^ 4 * b ^ 18 - a ^ 3 * b ^ 19 +
      a ^ 2 * b ^ 20 - a * b ^ 21 + b ^ 22) : ℤ) ∣ 23 := by
  set D := Int.gcd (a + b) (a ^ 22 - a ^ 21 * b + a ^ 20 * b ^ 2 - a ^ 19 * b ^ 3 +
      a ^ 18 * b ^ 4 - a ^ 17 * b ^ 5 + a ^ 16 * b ^ 6 - a ^ 15 * b ^ 7 + a ^ 14 * b ^ 8 -
      a ^ 13 * b ^ 9 + a ^ 12 * b ^ 10 - a ^ 11 * b ^ 11 + a ^ 10 * b ^ 12 - a ^ 9 * b ^ 13 +
      a ^ 8 * b ^ 14 - a ^ 7 * b ^ 15 + a ^ 6 * b ^ 16 - a ^ 5 * b ^ 17 + a ^ 4 * b ^ 18 -
      a ^ 3 * b ^ 19 + a ^ 2 * b ^ 20 - a * b ^ 21 + b ^ 22)
  have hD_ab  : (D : ℤ) ∣ (a + b) := Int.gcd_dvd_left _ _
  have hD_phi : (D : ℤ) ∣ (a ^ 22 - a ^ 21 * b + a ^ 20 * b ^ 2 - a ^ 19 * b ^ 3 +
      a ^ 18 * b ^ 4 - a ^ 17 * b ^ 5 + a ^ 16 * b ^ 6 - a ^ 15 * b ^ 7 + a ^ 14 * b ^ 8 -
      a ^ 13 * b ^ 9 + a ^ 12 * b ^ 10 - a ^ 11 * b ^ 11 + a ^ 10 * b ^ 12 - a ^ 9 * b ^ 13 +
      a ^ 8 * b ^ 14 - a ^ 7 * b ^ 15 + a ^ 6 * b ^ 16 - a ^ 5 * b ^ 17 + a ^ 4 * b ^ 18 -
      a ^ 3 * b ^ 19 + a ^ 2 * b ^ 20 - a * b ^ 21 + b ^ 22) :=
    Int.gcd_dvd_right _ _
  have hD_23b22 : (D : ℤ) ∣ 23 * b ^ 22 := by
    obtain ⟨s, hs⟩ := hD_phi
    obtain ⟨t, ht⟩ := hD_ab
    exact ⟨s - t * (a ^ 21 - 2 * a ^ 20 * b + 3 * a ^ 19 * b ^ 2 - 4 * a ^ 18 * b ^ 3 +
        5 * a ^ 17 * b ^ 4 - 6 * a ^ 16 * b ^ 5 + 7 * a ^ 15 * b ^ 6 - 8 * a ^ 14 * b ^ 7 +
        9 * a ^ 13 * b ^ 8 - 10 * a ^ 12 * b ^ 9 + 11 * a ^ 11 * b ^ 10 - 12 * a ^ 10 * b ^ 11 +
        13 * a ^ 9 * b ^ 12 - 14 * a ^ 8 * b ^ 13 + 15 * a ^ 7 * b ^ 14 - 16 * a ^ 6 * b ^ 15 +
        17 * a ^ 5 * b ^ 16 - 18 * a ^ 4 * b ^ 17 + 19 * a ^ 3 * b ^ 18 - 20 * a ^ 2 * b ^ 19 +
        21 * a * b ^ 20 - 22 * b ^ 21), by
      have key : 23 * b ^ 22 =
          (a ^ 22 - a ^ 21 * b + a ^ 20 * b ^ 2 - a ^ 19 * b ^ 3 + a ^ 18 * b ^ 4 -
          a ^ 17 * b ^ 5 + a ^ 16 * b ^ 6 - a ^ 15 * b ^ 7 + a ^ 14 * b ^ 8 - a ^ 13 * b ^ 9 +
          a ^ 12 * b ^ 10 - a ^ 11 * b ^ 11 + a ^ 10 * b ^ 12 - a ^ 9 * b ^ 13 + a ^ 8 * b ^ 14 -
          a ^ 7 * b ^ 15 + a ^ 6 * b ^ 16 - a ^ 5 * b ^ 17 + a ^ 4 * b ^ 18 - a ^ 3 * b ^ 19 +
          a ^ 2 * b ^ 20 - a * b ^ 21 + b ^ 22) -
          (a + b) * (a ^ 21 - 2 * a ^ 20 * b + 3 * a ^ 19 * b ^ 2 - 4 * a ^ 18 * b ^ 3 +
          5 * a ^ 17 * b ^ 4 - 6 * a ^ 16 * b ^ 5 + 7 * a ^ 15 * b ^ 6 - 8 * a ^ 14 * b ^ 7 +
          9 * a ^ 13 * b ^ 8 - 10 * a ^ 12 * b ^ 9 + 11 * a ^ 11 * b ^ 10 - 12 * a ^ 10 * b ^ 11 +
          13 * a ^ 9 * b ^ 12 - 14 * a ^ 8 * b ^ 13 + 15 * a ^ 7 * b ^ 14 - 16 * a ^ 6 * b ^ 15 +
          17 * a ^ 5 * b ^ 16 - 18 * a ^ 4 * b ^ 17 + 19 * a ^ 3 * b ^ 18 - 20 * a ^ 2 * b ^ 19 +
          21 * a * b ^ 20 - 22 * b ^ 21) := by ring
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
  have hcop_D_b22 : Nat.Coprime D (b ^ 22).natAbs := by
    rw [Int.natAbs_pow]; exact hcop_D_b.pow_right 22
  have hD_dvd_23b22_nat : D ∣ 23 * (b ^ 22).natAbs := by
    have h := Int.natAbs_dvd_natAbs.mpr hD_23b22
    rw [Int.natAbs_mul] at h; norm_cast at h
  exact_mod_cast hcop_D_b22.dvd_of_dvd_mul_right hD_dvd_23b22_nat
