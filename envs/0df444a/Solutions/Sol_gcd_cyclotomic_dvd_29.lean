-- Prove2me | solution 1 for gcd_cyclotomic_dvd_29
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-12T07:45:37.326641+00:00
-- url     : https://prove2.me/submissions/2a70c355-03cd-4b14-87a0-50cfc025ec30

import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.Ring

-- Q29 = sum_{k=0}^{27} (-1)^k*(k+1)*a^(27-k)*b^k  (28 terms, degree 27)
-- Key: 29*b^28 = Phi29(a,b) - (a+b)*Q29(a,b)

theorem solution (a b : ℤ) (hab : Int.gcd a b = 1) :
    (Int.gcd (a + b) (a ^ 28 - a ^ 27 * b + a ^ 26 * b ^ 2 - a ^ 25 * b ^ 3 + a ^ 24 * b ^ 4 -
      a ^ 23 * b ^ 5 + a ^ 22 * b ^ 6 - a ^ 21 * b ^ 7 + a ^ 20 * b ^ 8 - a ^ 19 * b ^ 9 +
      a ^ 18 * b ^ 10 - a ^ 17 * b ^ 11 + a ^ 16 * b ^ 12 - a ^ 15 * b ^ 13 + a ^ 14 * b ^ 14 -
      a ^ 13 * b ^ 15 + a ^ 12 * b ^ 16 - a ^ 11 * b ^ 17 + a ^ 10 * b ^ 18 - a ^ 9 * b ^ 19 +
      a ^ 8 * b ^ 20 - a ^ 7 * b ^ 21 + a ^ 6 * b ^ 22 - a ^ 5 * b ^ 23 + a ^ 4 * b ^ 24 -
      a ^ 3 * b ^ 25 + a ^ 2 * b ^ 26 - a * b ^ 27 + b ^ 28) : ℤ) ∣ 29 := by
  set D := Int.gcd (a + b) (a ^ 28 - a ^ 27 * b + a ^ 26 * b ^ 2 - a ^ 25 * b ^ 3 +
      a ^ 24 * b ^ 4 - a ^ 23 * b ^ 5 + a ^ 22 * b ^ 6 - a ^ 21 * b ^ 7 + a ^ 20 * b ^ 8 -
      a ^ 19 * b ^ 9 + a ^ 18 * b ^ 10 - a ^ 17 * b ^ 11 + a ^ 16 * b ^ 12 - a ^ 15 * b ^ 13 +
      a ^ 14 * b ^ 14 - a ^ 13 * b ^ 15 + a ^ 12 * b ^ 16 - a ^ 11 * b ^ 17 + a ^ 10 * b ^ 18 -
      a ^ 9 * b ^ 19 + a ^ 8 * b ^ 20 - a ^ 7 * b ^ 21 + a ^ 6 * b ^ 22 - a ^ 5 * b ^ 23 +
      a ^ 4 * b ^ 24 - a ^ 3 * b ^ 25 + a ^ 2 * b ^ 26 - a * b ^ 27 + b ^ 28)
  have hD_ab  : (D : ℤ) ∣ (a + b) := Int.gcd_dvd_left _ _
  have hD_phi : (D : ℤ) ∣ (a ^ 28 - a ^ 27 * b + a ^ 26 * b ^ 2 - a ^ 25 * b ^ 3 +
      a ^ 24 * b ^ 4 - a ^ 23 * b ^ 5 + a ^ 22 * b ^ 6 - a ^ 21 * b ^ 7 + a ^ 20 * b ^ 8 -
      a ^ 19 * b ^ 9 + a ^ 18 * b ^ 10 - a ^ 17 * b ^ 11 + a ^ 16 * b ^ 12 - a ^ 15 * b ^ 13 +
      a ^ 14 * b ^ 14 - a ^ 13 * b ^ 15 + a ^ 12 * b ^ 16 - a ^ 11 * b ^ 17 + a ^ 10 * b ^ 18 -
      a ^ 9 * b ^ 19 + a ^ 8 * b ^ 20 - a ^ 7 * b ^ 21 + a ^ 6 * b ^ 22 - a ^ 5 * b ^ 23 +
      a ^ 4 * b ^ 24 - a ^ 3 * b ^ 25 + a ^ 2 * b ^ 26 - a * b ^ 27 + b ^ 28) :=
    Int.gcd_dvd_right _ _
  have hD_29b28 : (D : ℤ) ∣ 29 * b ^ 28 := by
    obtain ⟨s, hs⟩ := hD_phi
    obtain ⟨t, ht⟩ := hD_ab
    exact ⟨s - t * (a ^ 27 - 2 * a ^ 26 * b + 3 * a ^ 25 * b ^ 2 - 4 * a ^ 24 * b ^ 3 +
        5 * a ^ 23 * b ^ 4 - 6 * a ^ 22 * b ^ 5 + 7 * a ^ 21 * b ^ 6 - 8 * a ^ 20 * b ^ 7 +
        9 * a ^ 19 * b ^ 8 - 10 * a ^ 18 * b ^ 9 + 11 * a ^ 17 * b ^ 10 - 12 * a ^ 16 * b ^ 11 +
        13 * a ^ 15 * b ^ 12 - 14 * a ^ 14 * b ^ 13 + 15 * a ^ 13 * b ^ 14 - 16 * a ^ 12 * b ^ 15 +
        17 * a ^ 11 * b ^ 16 - 18 * a ^ 10 * b ^ 17 + 19 * a ^ 9 * b ^ 18 - 20 * a ^ 8 * b ^ 19 +
        21 * a ^ 7 * b ^ 20 - 22 * a ^ 6 * b ^ 21 + 23 * a ^ 5 * b ^ 22 - 24 * a ^ 4 * b ^ 23 +
        25 * a ^ 3 * b ^ 24 - 26 * a ^ 2 * b ^ 25 + 27 * a * b ^ 26 - 28 * b ^ 27), by
      have key : 29 * b ^ 28 =
          (a ^ 28 - a ^ 27 * b + a ^ 26 * b ^ 2 - a ^ 25 * b ^ 3 + a ^ 24 * b ^ 4 -
          a ^ 23 * b ^ 5 + a ^ 22 * b ^ 6 - a ^ 21 * b ^ 7 + a ^ 20 * b ^ 8 - a ^ 19 * b ^ 9 +
          a ^ 18 * b ^ 10 - a ^ 17 * b ^ 11 + a ^ 16 * b ^ 12 - a ^ 15 * b ^ 13 +
          a ^ 14 * b ^ 14 - a ^ 13 * b ^ 15 + a ^ 12 * b ^ 16 - a ^ 11 * b ^ 17 +
          a ^ 10 * b ^ 18 - a ^ 9 * b ^ 19 + a ^ 8 * b ^ 20 - a ^ 7 * b ^ 21 +
          a ^ 6 * b ^ 22 - a ^ 5 * b ^ 23 + a ^ 4 * b ^ 24 - a ^ 3 * b ^ 25 +
          a ^ 2 * b ^ 26 - a * b ^ 27 + b ^ 28) -
          (a + b) * (a ^ 27 - 2 * a ^ 26 * b + 3 * a ^ 25 * b ^ 2 - 4 * a ^ 24 * b ^ 3 +
          5 * a ^ 23 * b ^ 4 - 6 * a ^ 22 * b ^ 5 + 7 * a ^ 21 * b ^ 6 - 8 * a ^ 20 * b ^ 7 +
          9 * a ^ 19 * b ^ 8 - 10 * a ^ 18 * b ^ 9 + 11 * a ^ 17 * b ^ 10 - 12 * a ^ 16 * b ^ 11 +
          13 * a ^ 15 * b ^ 12 - 14 * a ^ 14 * b ^ 13 + 15 * a ^ 13 * b ^ 14 - 16 * a ^ 12 * b ^ 15 +
          17 * a ^ 11 * b ^ 16 - 18 * a ^ 10 * b ^ 17 + 19 * a ^ 9 * b ^ 18 - 20 * a ^ 8 * b ^ 19 +
          21 * a ^ 7 * b ^ 20 - 22 * a ^ 6 * b ^ 21 + 23 * a ^ 5 * b ^ 22 - 24 * a ^ 4 * b ^ 23 +
          25 * a ^ 3 * b ^ 24 - 26 * a ^ 2 * b ^ 25 + 27 * a * b ^ 26 - 28 * b ^ 27) := by ring
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
  have hcop_D_b28 : Nat.Coprime D (b ^ 28).natAbs := by
    rw [Int.natAbs_pow]; exact hcop_D_b.pow_right 28
  have hD_dvd_29b28_nat : D ∣ 29 * (b ^ 28).natAbs := by
    have h := Int.natAbs_dvd_natAbs.mpr hD_29b28
    rw [Int.natAbs_mul] at h; norm_cast at h
  exact_mod_cast hcop_D_b28.dvd_of_dvd_mul_right hD_dvd_29b28_nat
