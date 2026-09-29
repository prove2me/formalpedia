-- Prove2me | solution 1 for syracuse_five_cycle_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-08T20:13:21.975791+00:00
-- url     : https://prove2.me/submissions/e6a45b49-7075-4358-8468-c33989ee964a

import Mathlib
import Definitions.Def_syracuseStep

open Nat

theorem gen (u v k : ℕ) (h : k ≤ v) : k * u ≤ u * v := by
  calc k * u = u * k := by ring
    _ ≤ u * v := Nat.mul_le_mul_left _ h

theorem five_bound (a b c d e : ℕ) (ha : 33 ≤ a) (hb : 33 ≤ b) (hc : 33 ≤ c)
    (hd : 33 ≤ d) (he : 33 ≤ e) :
    81 * (a*b*c*d + a*b*c*e + a*b*d*e + a*c*d*e + b*c*d*e)
      + 27 * (a*b*c + a*b*d + a*b*e + a*c*d + a*c*e + a*d*e + b*c*d + b*c*e + b*d*e + c*d*e)
      + 9 * (a*b + a*c + a*d + a*e + b*c + b*d + b*e + c*d + c*e + d*e)
      + 3 * (a + b + c + d + e) + 1 < 13 * (a*b*c*d*e) := by
  have nab : 1089 ≤ a * b := by
    calc (1089:ℕ) = 33 * 33 := by norm_num
      _ ≤ a * b := Nat.mul_le_mul ha hb
  have nac : 1089 ≤ a * c := by
    calc (1089:ℕ) = 33 * 33 := by norm_num
      _ ≤ a * c := Nat.mul_le_mul ha hc
  have nad : 1089 ≤ a * d := by
    calc (1089:ℕ) = 33 * 33 := by norm_num
      _ ≤ a * d := Nat.mul_le_mul ha hd
  have nae : 1089 ≤ a * e := by
    calc (1089:ℕ) = 33 * 33 := by norm_num
      _ ≤ a * e := Nat.mul_le_mul ha he
  have nbc : 1089 ≤ b * c := by
    calc (1089:ℕ) = 33 * 33 := by norm_num
      _ ≤ b * c := Nat.mul_le_mul hb hc
  have nbd : 1089 ≤ b * d := by
    calc (1089:ℕ) = 33 * 33 := by norm_num
      _ ≤ b * d := Nat.mul_le_mul hb hd
  have nbe : 1089 ≤ b * e := by
    calc (1089:ℕ) = 33 * 33 := by norm_num
      _ ≤ b * e := Nat.mul_le_mul hb he
  have ncd : 1089 ≤ c * d := by
    calc (1089:ℕ) = 33 * 33 := by norm_num
      _ ≤ c * d := Nat.mul_le_mul hc hd
  have nce : 1089 ≤ c * e := by
    calc (1089:ℕ) = 33 * 33 := by norm_num
      _ ≤ c * e := Nat.mul_le_mul hc he
  have nde : 1089 ≤ d * e := by
    calc (1089:ℕ) = 33 * 33 := by norm_num
      _ ≤ d * e := Nat.mul_le_mul hd he
  have nabc : 35937 ≤ a * b * c := by
    calc (35937:ℕ) = 1089 * 33 := by norm_num
      _ ≤ a * b * c := Nat.mul_le_mul nab hc
  have nabd : 35937 ≤ a * b * d := by
    calc (35937:ℕ) = 1089 * 33 := by norm_num
      _ ≤ a * b * d := Nat.mul_le_mul nab hd
  have nabe : 35937 ≤ a * b * e := by
    calc (35937:ℕ) = 1089 * 33 := by norm_num
      _ ≤ a * b * e := Nat.mul_le_mul nab he
  have nacd : 35937 ≤ a * c * d := by
    calc (35937:ℕ) = 1089 * 33 := by norm_num
      _ ≤ a * c * d := Nat.mul_le_mul nac hd
  have nace : 35937 ≤ a * c * e := by
    calc (35937:ℕ) = 1089 * 33 := by norm_num
      _ ≤ a * c * e := Nat.mul_le_mul nac he
  have nade : 35937 ≤ a * d * e := by
    calc (35937:ℕ) = 1089 * 33 := by norm_num
      _ ≤ a * d * e := Nat.mul_le_mul nad he
  have nbcd : 35937 ≤ b * c * d := by
    calc (35937:ℕ) = 1089 * 33 := by norm_num
      _ ≤ b * c * d := Nat.mul_le_mul nbc hd
  have nbce : 35937 ≤ b * c * e := by
    calc (35937:ℕ) = 1089 * 33 := by norm_num
      _ ≤ b * c * e := Nat.mul_le_mul nbc he
  have nbde : 35937 ≤ b * d * e := by
    calc (35937:ℕ) = 1089 * 33 := by norm_num
      _ ≤ b * d * e := Nat.mul_le_mul nbd he
  have ncde : 35937 ≤ c * d * e := by
    calc (35937:ℕ) = 1089 * 33 := by norm_num
      _ ≤ c * d * e := Nat.mul_le_mul ncd he
  have nabcd : 1185921 ≤ a * b * c * d := by
    calc (1185921:ℕ) = 35937 * 33 := by norm_num
      _ ≤ a * b * c * d := Nat.mul_le_mul nabc hd
  have nabce : 1185921 ≤ a * b * c * e := by
    calc (1185921:ℕ) = 35937 * 33 := by norm_num
      _ ≤ a * b * c * e := Nat.mul_le_mul nabc he
  have nabde : 1185921 ≤ a * b * d * e := by
    calc (1185921:ℕ) = 35937 * 33 := by norm_num
      _ ≤ a * b * d * e := Nat.mul_le_mul nabd he
  have nacde : 1185921 ≤ a * c * d * e := by
    calc (1185921:ℕ) = 35937 * 33 := by norm_num
      _ ≤ a * c * d * e := Nat.mul_le_mul nacd he
  have nbcde : 1185921 ≤ b * c * d * e := by
    calc (1185921:ℕ) = 35937 * 33 := by norm_num
      _ ≤ b * c * d * e := Nat.mul_le_mul nbcd he
  have nabcde : 39135393 ≤ a * b * c * d * e := by
    calc (39135393:ℕ) = 1185921 * 33 := by norm_num
      _ ≤ a * b * c * d * e := Nat.mul_le_mul nabcd he
  have Fabcd : 33 * (a * b * c * d) ≤ a*b*c*d*e := by
    calc 33 * (a * b * c * d) ≤ (a * b * c * d) * (e) := gen _ _ _ he
      _ = a*b*c*d*e := by ring
  have Fabce : 33 * (a * b * c * e) ≤ a*b*c*d*e := by
    calc 33 * (a * b * c * e) ≤ (a * b * c * e) * (d) := gen _ _ _ hd
      _ = a*b*c*d*e := by ring
  have Fabde : 33 * (a * b * d * e) ≤ a*b*c*d*e := by
    calc 33 * (a * b * d * e) ≤ (a * b * d * e) * (c) := gen _ _ _ hc
      _ = a*b*c*d*e := by ring
  have Facde : 33 * (a * c * d * e) ≤ a*b*c*d*e := by
    calc 33 * (a * c * d * e) ≤ (a * c * d * e) * (b) := gen _ _ _ hb
      _ = a*b*c*d*e := by ring
  have Fbcde : 33 * (b * c * d * e) ≤ a*b*c*d*e := by
    calc 33 * (b * c * d * e) ≤ (b * c * d * e) * (a) := gen _ _ _ ha
      _ = a*b*c*d*e := by ring
  have Fabc : 1089 * (a * b * c) ≤ a*b*c*d*e := by
    calc 1089 * (a * b * c) ≤ (a * b * c) * (d * e) := gen _ _ _ nde
      _ = a*b*c*d*e := by ring
  have Fabd : 1089 * (a * b * d) ≤ a*b*c*d*e := by
    calc 1089 * (a * b * d) ≤ (a * b * d) * (c * e) := gen _ _ _ nce
      _ = a*b*c*d*e := by ring
  have Fabe : 1089 * (a * b * e) ≤ a*b*c*d*e := by
    calc 1089 * (a * b * e) ≤ (a * b * e) * (c * d) := gen _ _ _ ncd
      _ = a*b*c*d*e := by ring
  have Facd : 1089 * (a * c * d) ≤ a*b*c*d*e := by
    calc 1089 * (a * c * d) ≤ (a * c * d) * (b * e) := gen _ _ _ nbe
      _ = a*b*c*d*e := by ring
  have Face : 1089 * (a * c * e) ≤ a*b*c*d*e := by
    calc 1089 * (a * c * e) ≤ (a * c * e) * (b * d) := gen _ _ _ nbd
      _ = a*b*c*d*e := by ring
  have Fade : 1089 * (a * d * e) ≤ a*b*c*d*e := by
    calc 1089 * (a * d * e) ≤ (a * d * e) * (b * c) := gen _ _ _ nbc
      _ = a*b*c*d*e := by ring
  have Fbcd : 1089 * (b * c * d) ≤ a*b*c*d*e := by
    calc 1089 * (b * c * d) ≤ (b * c * d) * (a * e) := gen _ _ _ nae
      _ = a*b*c*d*e := by ring
  have Fbce : 1089 * (b * c * e) ≤ a*b*c*d*e := by
    calc 1089 * (b * c * e) ≤ (b * c * e) * (a * d) := gen _ _ _ nad
      _ = a*b*c*d*e := by ring
  have Fbde : 1089 * (b * d * e) ≤ a*b*c*d*e := by
    calc 1089 * (b * d * e) ≤ (b * d * e) * (a * c) := gen _ _ _ nac
      _ = a*b*c*d*e := by ring
  have Fcde : 1089 * (c * d * e) ≤ a*b*c*d*e := by
    calc 1089 * (c * d * e) ≤ (c * d * e) * (a * b) := gen _ _ _ nab
      _ = a*b*c*d*e := by ring
  have Fab : 35937 * (a * b) ≤ a*b*c*d*e := by
    calc 35937 * (a * b) ≤ (a * b) * (c * d * e) := gen _ _ _ ncde
      _ = a*b*c*d*e := by ring
  have Fac : 35937 * (a * c) ≤ a*b*c*d*e := by
    calc 35937 * (a * c) ≤ (a * c) * (b * d * e) := gen _ _ _ nbde
      _ = a*b*c*d*e := by ring
  have Fad : 35937 * (a * d) ≤ a*b*c*d*e := by
    calc 35937 * (a * d) ≤ (a * d) * (b * c * e) := gen _ _ _ nbce
      _ = a*b*c*d*e := by ring
  have Fae : 35937 * (a * e) ≤ a*b*c*d*e := by
    calc 35937 * (a * e) ≤ (a * e) * (b * c * d) := gen _ _ _ nbcd
      _ = a*b*c*d*e := by ring
  have Fbc : 35937 * (b * c) ≤ a*b*c*d*e := by
    calc 35937 * (b * c) ≤ (b * c) * (a * d * e) := gen _ _ _ nade
      _ = a*b*c*d*e := by ring
  have Fbd : 35937 * (b * d) ≤ a*b*c*d*e := by
    calc 35937 * (b * d) ≤ (b * d) * (a * c * e) := gen _ _ _ nace
      _ = a*b*c*d*e := by ring
  have Fbe : 35937 * (b * e) ≤ a*b*c*d*e := by
    calc 35937 * (b * e) ≤ (b * e) * (a * c * d) := gen _ _ _ nacd
      _ = a*b*c*d*e := by ring
  have Fcd : 35937 * (c * d) ≤ a*b*c*d*e := by
    calc 35937 * (c * d) ≤ (c * d) * (a * b * e) := gen _ _ _ nabe
      _ = a*b*c*d*e := by ring
  have Fce : 35937 * (c * e) ≤ a*b*c*d*e := by
    calc 35937 * (c * e) ≤ (c * e) * (a * b * d) := gen _ _ _ nabd
      _ = a*b*c*d*e := by ring
  have Fde : 35937 * (d * e) ≤ a*b*c*d*e := by
    calc 35937 * (d * e) ≤ (d * e) * (a * b * c) := gen _ _ _ nabc
      _ = a*b*c*d*e := by ring
  have Fa : 1185921 * (a) ≤ a*b*c*d*e := by
    calc 1185921 * (a) ≤ (a) * (b * c * d * e) := gen _ _ _ nbcde
      _ = a*b*c*d*e := by ring
  have Fb : 1185921 * (b) ≤ a*b*c*d*e := by
    calc 1185921 * (b) ≤ (b) * (a * c * d * e) := gen _ _ _ nacde
      _ = a*b*c*d*e := by ring
  have Fc : 1185921 * (c) ≤ a*b*c*d*e := by
    calc 1185921 * (c) ≤ (c) * (a * b * d * e) := gen _ _ _ nabde
      _ = a*b*c*d*e := by ring
  have Fd : 1185921 * (d) ≤ a*b*c*d*e := by
    calc 1185921 * (d) ≤ (d) * (a * b * c * e) := gen _ _ _ nabce
      _ = a*b*c*d*e := by ring
  have Fe : 1185921 * (e) ≤ a*b*c*d*e := by
    calc 1185921 * (e) ≤ (e) * (a * b * c * d) := gen _ _ _ nabcd
      _ = a*b*c*d*e := by ring
  have F0 : 39135393 ≤ a*b*c*d*e := nabcde
  obtain ⟨P, dP⟩ : ∃ p, a*b*c*d*e = p := ⟨_, rfl⟩
  obtain ⟨X4, d4⟩ : ∃ q, a * b * c * d + a * b * c * e + a * b * d * e + a * c * d * e + b * c * d * e = q := ⟨_, rfl⟩
  obtain ⟨X3, d3⟩ : ∃ q, a * b * c + a * b * d + a * b * e + a * c * d + a * c * e + a * d * e + b * c * d + b * c * e + b * d * e + c * d * e = q := ⟨_, rfl⟩
  obtain ⟨X2, d2⟩ : ∃ q, a * b + a * c + a * d + a * e + b * c + b * d + b * e + c * d + c * e + d * e = q := ⟨_, rfl⟩
  obtain ⟨X1, d1⟩ : ∃ q, a + b + c + d + e = q := ⟨_, rfl⟩
  have A4 : 33 * X4 ≤ 5 * P := by
    rw [← d4, ← dP]; linarith [Fabcd, Fabce, Fabde, Facde, Fbcde]
  have A3 : 1089 * X3 ≤ 10 * P := by
    rw [← d3, ← dP]; linarith [Fabc, Fabd, Fabe, Facd, Face, Fade, Fbcd, Fbce, Fbde, Fcde]
  have A2 : 35937 * X2 ≤ 10 * P := by
    rw [← d2, ← dP]; linarith [Fab, Fac, Fad, Fae, Fbc, Fbd, Fbe, Fcd, Fce, Fde]
  have A1 : 1185921 * X1 ≤ 5 * P := by
    rw [← d1, ← dP]; linarith [Fa, Fb, Fc, Fd, Fe]
  rw [dP] at F0
  rw [d4, d3, d2, d1, dP]
  omega
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

theorem S1 : syracuseStep 1 = 1 := stepEq 2 (by norm_num) (by decide)
theorem S3 : syracuseStep 3 = 5 := stepEq 1 (by norm_num) (by decide)
theorem S5 : syracuseStep 5 = 1 := stepEq 4 (by norm_num) (by decide)
theorem S7 : syracuseStep 7 = 11 := stepEq 1 (by norm_num) (by decide)
theorem S9 : syracuseStep 9 = 7 := stepEq 2 (by norm_num) (by decide)
theorem S11 : syracuseStep 11 = 17 := stepEq 1 (by norm_num) (by decide)
theorem S13 : syracuseStep 13 = 5 := stepEq 3 (by norm_num) (by decide)
theorem S15 : syracuseStep 15 = 23 := stepEq 1 (by norm_num) (by decide)
theorem S17 : syracuseStep 17 = 13 := stepEq 2 (by norm_num) (by decide)
theorem S19 : syracuseStep 19 = 29 := stepEq 1 (by norm_num) (by decide)
theorem S21 : syracuseStep 21 = 1 := stepEq 6 (by norm_num) (by decide)
theorem S23 : syracuseStep 23 = 35 := stepEq 1 (by norm_num) (by decide)
theorem S25 : syracuseStep 25 = 19 := stepEq 2 (by norm_num) (by decide)
theorem S27 : syracuseStep 27 = 41 := stepEq 1 (by norm_num) (by decide)
theorem S29 : syracuseStep 29 = 11 := stepEq 3 (by norm_num) (by decide)
theorem S31 : syracuseStep 31 = 47 := stepEq 1 (by norm_num) (by decide)
theorem S35 : syracuseStep 35 = 53 := stepEq 1 (by norm_num) (by decide)
theorem S41 : syracuseStep 41 = 31 := stepEq 2 (by norm_num) (by decide)
theorem S47 : syracuseStep 47 = 71 := stepEq 1 (by norm_num) (by decide)
theorem S53 : syracuseStep 53 = 5 := stepEq 5 (by norm_num) (by decide)
theorem S71 : syracuseStep 71 = 107 := stepEq 1 (by norm_num) (by decide)
theorem S107 : syracuseStep 107 = 161 := stepEq 1 (by norm_num) (by decide)
theorem S161 : syracuseStep 161 = 121 := stepEq 2 (by norm_num) (by decide)

theorem small5 (y : ℕ) (hy : 0 < y) (hodd : Odd y) (hlt : y < 33)
    (hper : syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep y)))) = y) :
    y = 1 := by
  rw [Nat.odd_iff] at hodd
  interval_cases y
  · rfl
  · omega
  · rw [S3, S5, S1, S1, S1] at hper; omega
  · omega
  · rw [S5, S1, S1, S1, S1] at hper; omega
  · omega
  · rw [S7, S11, S17, S13, S5] at hper; omega
  · omega
  · rw [S9, S7, S11, S17, S13] at hper; omega
  · omega
  · rw [S11, S17, S13, S5, S1] at hper; omega
  · omega
  · rw [S13, S5, S1, S1, S1] at hper; omega
  · omega
  · rw [S15, S23, S35, S53, S5] at hper; omega
  · omega
  · rw [S17, S13, S5, S1, S1] at hper; omega
  · omega
  · rw [S19, S29, S11, S17, S13] at hper; omega
  · omega
  · rw [S21, S1, S1, S1, S1] at hper; omega
  · omega
  · rw [S23, S35, S53, S5, S1] at hper; omega
  · omega
  · rw [S25, S19, S29, S11, S17] at hper; omega
  · omega
  · rw [S27, S41, S31, S47, S71] at hper; omega
  · omega
  · rw [S29, S11, S17, S13, S5] at hper; omega
  · omega
  · rw [S31, S47, S71, S107, S161] at hper; omega
  · omega

set_option maxHeartbeats 400000 in
theorem solution (m : ℕ) (hm : 0 < m) (hcyc : syracuseStep^[5] m = m) : m = 1 := by
  have hc : syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep m)))) = m := by
    have h : syracuseStep^[5] m
        = syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep m)))) := by
      simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq]
    rwa [h] at hcyc
  obtain ⟨x1, hx1⟩ : ∃ y, syracuseStep m = y := ⟨_, rfl⟩
  obtain ⟨x2, hx2⟩ : ∃ y, syracuseStep x1 = y := ⟨_, rfl⟩
  obtain ⟨x3, hx3⟩ : ∃ y, syracuseStep x2 = y := ⟨_, rfl⟩
  obtain ⟨x4, hx4⟩ : ∃ y, syracuseStep x3 = y := ⟨_, rfl⟩
  rw [hx1, hx2, hx3, hx4] at hc
  have hx1p : 0 < x1 := hx1 ▸ stepPos
  have hx2p : 0 < x2 := hx2 ▸ stepPos
  have hx3p : 0 < x3 := hx3 ▸ stepPos
  have hx4p : 0 < x4 := hx4 ▸ stepPos
  have hmo : Odd m := hc ▸ stepOdd x4
  have ho1 : Odd x1 := hx1 ▸ stepOdd m
  have ho2 : Odd x2 := hx2 ▸ stepOdd x1
  have ho3 : Odd x3 := hx3 ▸ stepOdd x2
  have ho4 : Odd x4 := hx4 ▸ stepOdd x3
  obtain ⟨a0, e0⟩ : ∃ a, 2 ^ a * x1 = 3 * m + 1 := ⟨_, hx1 ▸ stepSplit m⟩
  obtain ⟨a1, e1⟩ : ∃ a, 2 ^ a * x2 = 3 * x1 + 1 := ⟨_, hx2 ▸ stepSplit x1⟩
  obtain ⟨a2, e2⟩ : ∃ a, 2 ^ a * x3 = 3 * x2 + 1 := ⟨_, hx3 ▸ stepSplit x2⟩
  obtain ⟨a3, e3⟩ : ∃ a, 2 ^ a * x4 = 3 * x3 + 1 := ⟨_, hx4 ▸ stepSplit x3⟩
  obtain ⟨a4, e4⟩ : ∃ a, 2 ^ a * m = 3 * x4 + 1 := ⟨_, hc ▸ stepSplit x4⟩
  have hP : 0 < m * x1 * x2 * x3 * x4 := by positivity
  have hprod : 2 ^ (a0 + a1 + a2 + a3 + a4) * (m * x1 * x2 * x3 * x4)
      = 243 * (m * x1 * x2 * x3 * x4) + 81 * (m * x1 * x2 * x3 + m * x1 * x2 * x4 + m * x1 * x3 * x4 + m * x2 * x3 * x4 + x1 * x2 * x3 * x4)
        + 27 * (m * x1 * x2 + m * x1 * x3 + m * x1 * x4 + m * x2 * x3 + m * x2 * x4 + m * x3 * x4 + x1 * x2 * x3 + x1 * x2 * x4 + x1 * x3 * x4 + x2 * x3 * x4)
        + 9 * (m * x1 + m * x2 + m * x3 + m * x4 + x1 * x2 + x1 * x3 + x1 * x4 + x2 * x3 + x2 * x4 + x3 * x4)
        + 3 * (m + x1 + x2 + x3 + x4) + 1 := by
    rw [pow_add, pow_add, pow_add, pow_add]
    calc 2 ^ a0 * 2 ^ a1 * 2 ^ a2 * 2 ^ a3 * 2 ^ a4 * (m * x1 * x2 * x3 * x4)
        = (2 ^ a0 * x1) * (2 ^ a1 * x2) * (2 ^ a2 * x3) * (2 ^ a3 * x4) * (2 ^ a4 * m) := by ring
      _ = (3 * m + 1) * (3 * x1 + 1) * (3 * x2 + 1) * (3 * x3 + 1) * (3 * x4 + 1) := by
          rw [e0, e1, e2, e3, e4]
      _ = _ := by ring
  have h243 : 243 < 2 ^ (a0 + a1 + a2 + a3 + a4) := by
    by_contra hcon
    push Not at hcon
    have hle := Nat.mul_le_mul_right (m * x1 * x2 * x3 * x4) hcon
    rw [hprod] at hle
    omega
  have h256 : 256 ≤ 2 ^ (a0 + a1 + a2 + a3 + a4) := by
    by_contra hcon
    push Not at hcon
    have hk : a0 + a1 + a2 + a3 + a4 ≤ 7 := by
      by_contra hkk
      push Not at hkk
      have h8 : (2:ℕ) ^ 8 ≤ 2 ^ (a0 + a1 + a2 + a3 + a4) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      norm_num at h8; omega
    have h7 : (2:ℕ) ^ (a0 + a1 + a2 + a3 + a4) ≤ 2 ^ 7 :=
      Nat.pow_le_pow_right (by norm_num) hk
    norm_num at h7; omega
  have hkey : 13 * (m * x1 * x2 * x3 * x4) ≤ 81 * (m * x1 * x2 * x3 + m * x1 * x2 * x4 + m * x1 * x3 * x4 + m * x2 * x3 * x4 + x1 * x2 * x3 * x4)
        + 27 * (m * x1 * x2 + m * x1 * x3 + m * x1 * x4 + m * x2 * x3 + m * x2 * x4 + m * x3 * x4 + x1 * x2 * x3 + x1 * x2 * x4 + x1 * x3 * x4 + x2 * x3 * x4)
        + 9 * (m * x1 + m * x2 + m * x3 + m * x4 + x1 * x2 + x1 * x3 + x1 * x4 + x2 * x3 + x2 * x4 + x3 * x4)
        + 3 * (m + x1 + x2 + x3 + x4) + 1 := by
    have h1 := Nat.mul_le_mul_right (m * x1 * x2 * x3 * x4) h256
    rw [hprod] at h1
    omega
  have hsmall : m = 1 ∨ x1 = 1 ∨ x2 = 1 ∨ x3 = 1 ∨ x4 = 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2, g3, g4⟩ := hcon
    have p5 : syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep m)))) = m := by
      rw [hx1, hx2, hx3, hx4, hc]
    have b0 : 33 ≤ m := by
      by_contra hb
      exact g0 (small5 m hm hmo (by omega) p5)
    have b1 : 33 ≤ x1 := by
      by_contra hb
      exact g1 (small5 x1 hx1p ho1 (by omega) (by rw [hx2, hx3, hx4, hc, hx1]))
    have b2 : 33 ≤ x2 := by
      by_contra hb
      exact g2 (small5 x2 hx2p ho2 (by omega) (by rw [hx3, hx4, hc, hx1, hx2]))
    have b3 : 33 ≤ x3 := by
      by_contra hb
      exact g3 (small5 x3 hx3p ho3 (by omega) (by rw [hx4, hc, hx1, hx2, hx3]))
    have b4 : 33 ≤ x4 := by
      by_contra hb
      exact g4 (small5 x4 hx4p ho4 (by omega) (by rw [hc, hx1, hx2, hx3, hx4]))
    exact absurd hkey (not_le.mpr (five_bound m x1 x2 x3 x4 b0 b1 b2 b3 b4))
  rcases hsmall with h | h | h | h | h
  · exact h
  · have q2 : x2 = 1 := by rw [← hx2, h, S1]
    have q3 : x3 = 1 := by rw [← hx3, q2, S1]
    have q4 : x4 = 1 := by rw [← hx4, q3, S1]
    rw [q4, S1] at hc; omega
  · have q3 : x3 = 1 := by rw [← hx3, h, S1]
    have q4 : x4 = 1 := by rw [← hx4, q3, S1]
    rw [q4, S1] at hc; omega
  · have q4 : x4 = 1 := by rw [← hx4, h, S1]
    rw [q4, S1] at hc; omega
  · rw [h, S1] at hc; omega
