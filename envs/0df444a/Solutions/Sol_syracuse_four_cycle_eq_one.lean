-- Prove2me | solution 1 for syracuse_four_cycle_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-08T20:01:20.895206+00:00
-- url     : https://prove2.me/submissions/d1978a98-1f11-4143-a2e3-446f7062cd79

import Mathlib
import Definitions.Def_syracuseStep

open Nat

theorem stepEq (a : ℕ) {y z : ℕ} (h : 3 * y + 1 = 2 ^ a * z) (hz : Odd z) :
    syracuseStep y = z := by
  have hz0 : z ≠ 0 := by rintro rfl; simp [Nat.odd_iff] at hz
  have hfac : (3 * y + 1).factorization 2 = a := by
    rw [h, Nat.factorization_mul (by positivity) hz0]
    simp [Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by rwa [Nat.two_dvd_ne_zero, ← Nat.odd_iff])]
  show ordCompl[2] (3 * y + 1) = z
  rw [hfac, h, Nat.mul_div_cancel_left _ (by positivity)]

theorem stepOdd (n : ℕ) : Odd (syracuseStep n) := by
  rw [Nat.odd_iff, ← Nat.not_even_iff]
  intro he
  exact Nat.not_dvd_ordCompl Nat.prime_two (by omega : 3 * n + 1 ≠ 0) he.two_dvd

theorem stepPos {n : ℕ} : 0 < syracuseStep n := Nat.ordCompl_pos 2 (by omega)

theorem stepSplit (n : ℕ) : 2 ^ ((3 * n + 1).factorization 2) * syracuseStep n = 3 * n + 1 :=
  Nat.ordProj_mul_ordCompl_eq_self (3 * n + 1) 2

-- the three small periodic checks
theorem T1 : syracuseStep 1 = 1 := stepEq 2 (by norm_num) (by decide)
theorem T3 : syracuseStep 3 = 5 := stepEq 1 (by norm_num) (by decide)
theorem T5 : syracuseStep 5 = 1 := stepEq 4 (by norm_num) (by decide)

theorem gen (u v k : ℕ) (h : k ≤ v) : k * u ≤ u * v := by
  calc k * u = u * k := by ring
    _ ≤ u * v := Nat.mul_le_mul_left _ h

theorem four_bound (a b c d : ℕ) (ha : 3 ≤ a) (hb : 3 ≤ b) (hc : 3 ≤ c) (hd : 3 ≤ d) :
    27 * (a * b * c + a * b * d + a * c * d + b * c * d)
      + 9 * (a * b + a * c + a * d + b * c + b * d + c * d)
      + 3 * (a + b + c + d) + 1 < 47 * (a * b * c * d) := by
  have n9_cd : 9 ≤ c * d := by nlinarith
  have n9_bd : 9 ≤ b * d := by nlinarith
  have n9_bc : 9 ≤ b * c := by nlinarith
  have n9_ad : 9 ≤ a * d := by nlinarith
  have n9_ac : 9 ≤ a * c := by nlinarith
  have n9_ab : 9 ≤ a * b := by nlinarith
  have n27_bcd : 27 ≤ b * c * d := by nlinarith [n9_cd]
  have n27_acd : 27 ≤ a * c * d := by nlinarith [n9_cd]
  have n27_abd : 27 ≤ a * b * d := by nlinarith [n9_bd]
  have n27_abc : 27 ≤ a * b * c := by nlinarith [n9_bc]
  have Tabc : 3 * (a * b * c) ≤ a * b * c * d := by
    calc 3 * (a * b * c) ≤ (a * b * c) * d := gen _ _ _ hd
      _ = a * b * c * d := by ring
  have Tabd : 3 * (a * b * d) ≤ a * b * c * d := by
    calc 3 * (a * b * d) ≤ (a * b * d) * c := gen _ _ _ hc
      _ = a * b * c * d := by ring
  have Tacd : 3 * (a * c * d) ≤ a * b * c * d := by
    calc 3 * (a * c * d) ≤ (a * c * d) * b := gen _ _ _ hb
      _ = a * b * c * d := by ring
  have Tbcd : 3 * (b * c * d) ≤ a * b * c * d := by
    calc 3 * (b * c * d) ≤ (b * c * d) * a := gen _ _ _ ha
      _ = a * b * c * d := by ring
  have Qab : 9 * (a * b) ≤ a * b * c * d := by
    calc 9 * (a * b) ≤ (a * b) * (c * d) := gen _ _ _ n9_cd
      _ = a * b * c * d := by ring
  have Qac : 9 * (a * c) ≤ a * b * c * d := by
    calc 9 * (a * c) ≤ (a * c) * (b * d) := gen _ _ _ n9_bd
      _ = a * b * c * d := by ring
  have Qad : 9 * (a * d) ≤ a * b * c * d := by
    calc 9 * (a * d) ≤ (a * d) * (b * c) := gen _ _ _ n9_bc
      _ = a * b * c * d := by ring
  have Qbc : 9 * (b * c) ≤ a * b * c * d := by
    calc 9 * (b * c) ≤ (b * c) * (a * d) := gen _ _ _ n9_ad
      _ = a * b * c * d := by ring
  have Qbd : 9 * (b * d) ≤ a * b * c * d := by
    calc 9 * (b * d) ≤ (b * d) * (a * c) := gen _ _ _ n9_ac
      _ = a * b * c * d := by ring
  have Qcd : 9 * (c * d) ≤ a * b * c * d := by
    calc 9 * (c * d) ≤ (c * d) * (a * b) := gen _ _ _ n9_ab
      _ = a * b * c * d := by ring
  have Sa : 27 * a ≤ a * b * c * d := by
    calc 27 * a ≤ a * (b * c * d) := gen _ _ _ n27_bcd
      _ = a * b * c * d := by ring
  have Sb : 27 * b ≤ a * b * c * d := by
    calc 27 * b ≤ b * (a * c * d) := gen _ _ _ n27_acd
      _ = a * b * c * d := by ring
  have Sc : 27 * c ≤ a * b * c * d := by
    calc 27 * c ≤ c * (a * b * d) := gen _ _ _ n27_abd
      _ = a * b * c * d := by ring
  have Sd : 27 * d ≤ a * b * c * d := by
    calc 27 * d ≤ d * (a * b * c) := gen _ _ _ n27_abc
      _ = a * b * c * d := by ring
  have R : 81 ≤ a * b * c * d := by nlinarith [n27_bcd]
  obtain ⟨P, dP⟩ : ∃ p, a * b * c * d = p := ⟨_, rfl⟩
  obtain ⟨E3, d3⟩ : ∃ q, a * b * c + a * b * d + a * c * d + b * c * d = q := ⟨_, rfl⟩
  obtain ⟨E2, d2⟩ : ∃ q, a * b + a * c + a * d + b * c + b * d + c * d = q := ⟨_, rfl⟩
  obtain ⟨E1, d1⟩ : ∃ q, a + b + c + d = q := ⟨_, rfl⟩
  have A : 3 * E3 ≤ 4 * P := by
    rw [← d3, ← dP]; linarith [Tabc, Tabd, Tacd, Tbcd]
  have B : 9 * E2 ≤ 6 * P := by
    rw [← d2, ← dP]; linarith [Qab, Qac, Qad, Qbc, Qbd, Qcd]
  have C : 27 * E1 ≤ 4 * P := by
    rw [← d1, ← dP]; linarith [Sa, Sb, Sc, Sd]
  rw [dP] at R
  rw [d3, d2, d1, dP]
  omega

set_option maxHeartbeats 400000 in
theorem solution (m : ℕ) (hm : 0 < m) (hcyc : syracuseStep^[4] m = m) : m = 1 := by
  have hc : syracuseStep (syracuseStep (syracuseStep (syracuseStep m))) = m := by
    have h : syracuseStep^[4] m
        = syracuseStep (syracuseStep (syracuseStep (syracuseStep m))) := by
      simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq]
    rwa [h] at hcyc
  obtain ⟨x1, hx1⟩ : ∃ y, syracuseStep m = y := ⟨_, rfl⟩
  obtain ⟨x2, hx2⟩ : ∃ y, syracuseStep x1 = y := ⟨_, rfl⟩
  obtain ⟨x3, hx3⟩ : ∃ y, syracuseStep x2 = y := ⟨_, rfl⟩
  rw [hx1, hx2, hx3] at hc
  have hmo : Odd m := hc ▸ stepOdd x3
  have hx1o : Odd x1 := hx1 ▸ stepOdd m
  have hx2o : Odd x2 := hx2 ▸ stepOdd x1
  have hx3o : Odd x3 := hx3 ▸ stepOdd x2
  obtain ⟨a0, e0⟩ : ∃ a, 2 ^ a * x1 = 3 * m + 1 := ⟨_, hx1 ▸ stepSplit m⟩
  obtain ⟨a1, e1⟩ : ∃ a, 2 ^ a * x2 = 3 * x1 + 1 := ⟨_, hx2 ▸ stepSplit x1⟩
  obtain ⟨a2, e2⟩ : ∃ a, 2 ^ a * x3 = 3 * x2 + 1 := ⟨_, hx3 ▸ stepSplit x2⟩
  obtain ⟨a3, e3⟩ : ∃ a, 2 ^ a * m = 3 * x3 + 1 := ⟨_, hc ▸ stepSplit x3⟩
  have hx1p : 0 < x1 := hx1 ▸ stepPos
  have hx2p : 0 < x2 := hx2 ▸ stepPos
  have hx3p : 0 < x3 := hx3 ▸ stepPos
  have hP : 0 < m * x1 * x2 * x3 := by positivity
  have hprod : 2 ^ (a0 + a1 + a2 + a3) * (m * x1 * x2 * x3)
      = 81 * (m * x1 * x2 * x3)
        + 27 * (m * x1 * x2 + m * x1 * x3 + m * x2 * x3 + x1 * x2 * x3)
        + 9 * (m * x1 + m * x2 + m * x3 + x1 * x2 + x1 * x3 + x2 * x3)
        + 3 * (m + x1 + x2 + x3) + 1 := by
    rw [pow_add, pow_add, pow_add]
    calc 2 ^ a0 * 2 ^ a1 * 2 ^ a2 * 2 ^ a3 * (m * x1 * x2 * x3)
        = (2 ^ a0 * x1) * (2 ^ a1 * x2) * (2 ^ a2 * x3) * (2 ^ a3 * m) := by ring
      _ = (3 * m + 1) * (3 * x1 + 1) * (3 * x2 + 1) * (3 * x3 + 1) := by rw [e0, e1, e2, e3]
      _ = _ := by ring
  have h81 : 81 < 2 ^ (a0 + a1 + a2 + a3) := by
    by_contra hcon
    push Not at hcon
    have hle := Nat.mul_le_mul_right (m * x1 * x2 * x3) hcon
    rw [hprod] at hle
    omega
  have h128 : 128 ≤ 2 ^ (a0 + a1 + a2 + a3) := by
    by_contra hcon
    push Not at hcon
    have hk : a0 + a1 + a2 + a3 ≤ 6 := by
      by_contra hkk
      push Not at hkk
      have h7 : (2:ℕ) ^ 7 ≤ 2 ^ (a0 + a1 + a2 + a3) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      norm_num at h7; omega
    have h6 : (2:ℕ) ^ (a0 + a1 + a2 + a3) ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hk
    norm_num at h6; omega
  have hkey : 47 * (m * x1 * x2 * x3)
      ≤ 27 * (m * x1 * x2 + m * x1 * x3 + m * x2 * x3 + x1 * x2 * x3)
        + 9 * (m * x1 + m * x2 + m * x3 + x1 * x2 + x1 * x3 + x2 * x3)
        + 3 * (m + x1 + x2 + x3) + 1 := by
    have h1 := Nat.mul_le_mul_right (m * x1 * x2 * x3) h128
    rw [hprod] at h1
    omega
  have hsmall : m = 1 ∨ x1 = 1 ∨ x2 = 1 ∨ x3 = 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2, g3⟩ := hcon
    have b0 : 3 ≤ m := by rcases hmo with ⟨k, hk⟩; omega
    have b1 : 3 ≤ x1 := by rcases hx1o with ⟨k, hk⟩; omega
    have b2 : 3 ≤ x2 := by rcases hx2o with ⟨k, hk⟩; omega
    have b3 : 3 ≤ x3 := by rcases hx3o with ⟨k, hk⟩; omega
    exact absurd hkey (not_le.mpr (four_bound m x1 x2 x3 b0 b1 b2 b3))
  rcases hsmall with h | h | h | h
  · exact h
  · have h2 : x2 = 1 := by rw [← hx2, h, T1]
    have h3 : x3 = 1 := by rw [← hx3, h2, T1]
    rw [h3, T1] at hc; omega
  · have h3 : x3 = 1 := by rw [← hx3, h, T1]
    rw [h3, T1] at hc; omega
  · rw [h, T1] at hc; omega
