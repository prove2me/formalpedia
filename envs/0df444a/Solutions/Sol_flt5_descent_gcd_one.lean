-- Prove2me | solution 1 for flt5_descent_gcd_one
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-12T07:01:23.998884+00:00
-- url     : https://prove2.me/submissions/c1c4b320-c4c2-4cb9-9cab-1c7b3f4d92a6

import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

theorem solution (a b c : ℤ) (h_eq : a ^ 5 + b ^ 5 = c ^ 5) (h_cop : Int.gcd a b = 1)
    (h_not5c : ¬(5 : ℤ) ∣ c) :
    Int.gcd (a + b) (a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4) = 1 := by
  set D := Int.gcd (a + b) (a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4) with hD_def
  -- Step 1: (D : ℤ) ∣ 5  (inlined from gcd_cyclotomic_dvd_5)
  have hD_dvd_5 : (D : ℤ) ∣ 5 := by
    have hD_ab  : (D : ℤ) ∣ (a + b) := Int.gcd_dvd_left _ _
    have hD_phi : (D : ℤ) ∣ (a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4) :=
      Int.gcd_dvd_right _ _
    have hD_5b4 : (D : ℤ) ∣ 5 * b ^ 4 := by
      obtain ⟨s, hs⟩ := hD_phi
      obtain ⟨t, ht⟩ := hD_ab
      exact ⟨s - t * (a ^ 3 - 2 * a ^ 2 * b + 3 * a * b ^ 2 - 4 * b ^ 3), by
        have key : 5 * b ^ 4 = (a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4) -
            (a + b) * (a ^ 3 - 2 * a ^ 2 * b + 3 * a * b ^ 2 - 4 * b ^ 3) := by ring
        rw [key, hs, ht]; ring⟩
    have hD_dvd_ab_nat : D ∣ (a + b).natAbs := by
      exact_mod_cast Int.natAbs_dvd_natAbs.mpr hD_ab
    have hgcd_ab_b : Int.gcd (a + b) b = 1 := by
      rw [Int.gcd_comm]
      have h := @Int.gcd_add_mul_right_right b a 1
      simp only [one_mul] at h
      rw [h, Int.gcd_comm]; exact h_cop
    have hcop_D_b : Nat.Coprime D b.natAbs := by
      unfold Nat.Coprime; apply Nat.eq_one_of_dvd_one
      have h1 := Nat.gcd_dvd_left D b.natAbs
      have h2 := Nat.gcd_dvd_right D b.natAbs
      have h3 : Nat.gcd D b.natAbs ∣ (a + b).natAbs := dvd_trans h1 hD_dvd_ab_nat
      have h4 := Nat.dvd_gcd h3 h2
      rwa [show Nat.gcd (a + b).natAbs b.natAbs = 1 from hgcd_ab_b] at h4
    have hcop_D_b4 : Nat.Coprime D (b ^ 4).natAbs := by
      rw [Int.natAbs_pow]; exact hcop_D_b.pow_right 4
    have hD_dvd_5b4_nat : D ∣ 5 * (b ^ 4).natAbs := by
      have h := Int.natAbs_dvd_natAbs.mpr hD_5b4
      rw [Int.natAbs_mul] at h; norm_cast at h
    exact_mod_cast hcop_D_b4.dvd_of_dvd_mul_right hD_dvd_5b4_nat
  -- Step 2–4: D ∈ ℕ, D ≥ 1, D ≤ 5
  have hD_dvd_5_nat : D ∣ 5 := by exact_mod_cast hD_dvd_5
  have hD_pos : 0 < D := by
    rcases Nat.eq_zero_or_pos D with h | h
    · have : (D : ℤ) = 0 := by exact_mod_cast h
      rw [this] at hD_dvd_5; norm_num at hD_dvd_5
    · exact h
  have hD_le_5 : D ≤ 5 := Nat.le_of_dvd (by norm_num) hD_dvd_5_nat
  -- Step 5: case split D ∈ {1,2,3,4,5}
  rcases (show D = 1 ∨ D = 2 ∨ D = 3 ∨ D = 4 ∨ D = 5 from by omega) with h | h | h | h | h
  · exact h
  · exact absurd (h ▸ hD_dvd_5_nat) (by norm_num)
  · exact absurd (h ▸ hD_dvd_5_nat) (by norm_num)
  · exact absurd (h ▸ hD_dvd_5_nat) (by norm_num)
  · -- D = 5: show 5 ∣ c → contradiction
    exfalso
    have hD_ab : (D : ℤ) ∣ (a + b) := Int.gcd_dvd_left _ _
    have hDeq : (D : ℤ) = 5 := by exact_mod_cast h
    have h5_ab : (5 : ℤ) ∣ (a + b) := by rw [← hDeq]; exact hD_ab
    have hfact : (a + b) * (a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4) = c ^ 5 :=
      (by ring : (a + b) * _ = a ^ 5 + b ^ 5).trans h_eq
    have h5_c5 : (5 : ℤ) ∣ c ^ 5 := hfact ▸ dvd_mul_of_dvd_left h5_ab _
    -- 5 | c^5 → 5 | c via Fermat: x^5 = x in ZMod 5
    have fermat5 : ∀ x : ZMod 5, x ^ 5 = x := by decide
    have hc5_zero : ((c : ℤ) : ZMod 5) ^ 5 = 0 := by
      have key : ((c ^ 5 : ℤ) : ZMod 5) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd (c ^ 5) 5).mpr h5_c5
      push_cast at key; exact key
    have hc_zero : ((c : ℤ) : ZMod 5) = 0 :=
      (fermat5 ((c : ℤ) : ZMod 5)).symm.trans hc5_zero
    exact h_not5c ((ZMod.intCast_zmod_eq_zero_iff_dvd c 5).mp hc_zero)
