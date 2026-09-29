-- Prove2me | solution 1 for syracuse_six_cycle_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-08T21:03:55.842311+00:00
-- url     : https://prove2.me/submissions/863e2939-a5f0-40d7-850f-b8114b3662ad

import Mathlib
import Definitions.Def_syracuseStep
import Theorems.Thm_syracuse_no_small_cycle

open Nat

theorem stepOdd (n : ℕ) : Odd (syracuseStep n) := by
  rw [Nat.odd_iff, ← Nat.not_even_iff]
  intro he
  exact Nat.not_dvd_ordCompl Nat.prime_two (by omega : 3 * n + 1 ≠ 0) he.two_dvd

theorem stepPos {n : ℕ} : 0 < syracuseStep n := Nat.ordCompl_pos 2 (by omega)

theorem stepSplit (n : ℕ) : 2 ^ ((3 * n + 1).factorization 2) * syracuseStep n = 3 * n + 1 :=
  Nat.ordProj_mul_ordCompl_eq_self (3 * n + 1) 2

theorem stepEq (a : ℕ) {y z : ℕ} (h : 3 * y + 1 = 2 ^ a * z) (hz : Odd z) :
    syracuseStep y = z := by
  have hz0 : z ≠ 0 := by rintro rfl; simp [Nat.odd_iff] at hz
  have hfac : (3 * y + 1).factorization 2 = a := by
    rw [h, Nat.factorization_mul (by positivity) hz0]
    simp [Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by rwa [Nat.two_dvd_ne_zero, ← Nat.odd_iff])]
  show ordCompl[2] (3 * y + 1) = z
  rw [hfac, h, Nat.mul_div_cancel_left _ (by positivity)]

theorem T1 : syracuseStep 1 = 1 := stepEq 2 (by norm_num) (by decide)

theorem gen (u v k : ℕ) (h : k ≤ v) : k * u ≤ u * v := by
  calc k * u = u * k := by ring
    _ ≤ u * v := Nat.mul_le_mul_left _ h


theorem six_bound (a b c d e f : ℕ) (ha : 7 ≤ a) (hb : 7 ≤ b) (hc : 7 ≤ c) (hd : 7 ≤ d) (he : 7 ≤ e) (hf : 7 ≤ f) :
    243 * (a * b * c * d * e + a * b * c * d * f + a * b * c * e * f + a * b * d * e * f + a * c * d * e * f + b * c * d * e * f) + 81 * (a * b * c * d + a * b * c * e + a * b * c * f + a * b * d * e + a * b * d * f + a * b * e * f + a * c * d * e + a * c * d * f + a * c * e * f + a * d * e * f + b * c * d * e + b * c * d * f + b * c * e * f + b * d * e * f + c * d * e * f) + 27 * (a * b * c + a * b * d + a * b * e + a * b * f + a * c * d + a * c * e + a * c * f + a * d * e + a * d * f + a * e * f + b * c * d + b * c * e + b * c * f + b * d * e + b * d * f + b * e * f + c * d * e + c * d * f + c * e * f + d * e * f) + 9 * (a * b + a * c + a * d + a * e + a * f + b * c + b * d + b * e + b * f + c * d + c * e + c * f + d * e + d * f + e * f) + 3 * (a + b + c + d + e + f) + 1 < 295 * (a * b * c * d * e * f) := by
  have nab : 49 ≤ a * b := by
    calc (49:ℕ) = 7 * 7 := by norm_num
      _ ≤ a * b := Nat.mul_le_mul ha hb
  have nac : 49 ≤ a * c := by
    calc (49:ℕ) = 7 * 7 := by norm_num
      _ ≤ a * c := Nat.mul_le_mul ha hc
  have nad : 49 ≤ a * d := by
    calc (49:ℕ) = 7 * 7 := by norm_num
      _ ≤ a * d := Nat.mul_le_mul ha hd
  have nae : 49 ≤ a * e := by
    calc (49:ℕ) = 7 * 7 := by norm_num
      _ ≤ a * e := Nat.mul_le_mul ha he
  have naf : 49 ≤ a * f := by
    calc (49:ℕ) = 7 * 7 := by norm_num
      _ ≤ a * f := Nat.mul_le_mul ha hf
  have nbc : 49 ≤ b * c := by
    calc (49:ℕ) = 7 * 7 := by norm_num
      _ ≤ b * c := Nat.mul_le_mul hb hc
  have nbd : 49 ≤ b * d := by
    calc (49:ℕ) = 7 * 7 := by norm_num
      _ ≤ b * d := Nat.mul_le_mul hb hd
  have nbe : 49 ≤ b * e := by
    calc (49:ℕ) = 7 * 7 := by norm_num
      _ ≤ b * e := Nat.mul_le_mul hb he
  have nbf : 49 ≤ b * f := by
    calc (49:ℕ) = 7 * 7 := by norm_num
      _ ≤ b * f := Nat.mul_le_mul hb hf
  have ncd : 49 ≤ c * d := by
    calc (49:ℕ) = 7 * 7 := by norm_num
      _ ≤ c * d := Nat.mul_le_mul hc hd
  have nce : 49 ≤ c * e := by
    calc (49:ℕ) = 7 * 7 := by norm_num
      _ ≤ c * e := Nat.mul_le_mul hc he
  have ncf : 49 ≤ c * f := by
    calc (49:ℕ) = 7 * 7 := by norm_num
      _ ≤ c * f := Nat.mul_le_mul hc hf
  have nde : 49 ≤ d * e := by
    calc (49:ℕ) = 7 * 7 := by norm_num
      _ ≤ d * e := Nat.mul_le_mul hd he
  have ndf : 49 ≤ d * f := by
    calc (49:ℕ) = 7 * 7 := by norm_num
      _ ≤ d * f := Nat.mul_le_mul hd hf
  have nef : 49 ≤ e * f := by
    calc (49:ℕ) = 7 * 7 := by norm_num
      _ ≤ e * f := Nat.mul_le_mul he hf
  have nabc : 343 ≤ a * b * c := by
    calc (343:ℕ) = 49 * 7 := by norm_num
      _ ≤ a * b * c := Nat.mul_le_mul nab hc
  have nabd : 343 ≤ a * b * d := by
    calc (343:ℕ) = 49 * 7 := by norm_num
      _ ≤ a * b * d := Nat.mul_le_mul nab hd
  have nabe : 343 ≤ a * b * e := by
    calc (343:ℕ) = 49 * 7 := by norm_num
      _ ≤ a * b * e := Nat.mul_le_mul nab he
  have nabf : 343 ≤ a * b * f := by
    calc (343:ℕ) = 49 * 7 := by norm_num
      _ ≤ a * b * f := Nat.mul_le_mul nab hf
  have nacd : 343 ≤ a * c * d := by
    calc (343:ℕ) = 49 * 7 := by norm_num
      _ ≤ a * c * d := Nat.mul_le_mul nac hd
  have nace : 343 ≤ a * c * e := by
    calc (343:ℕ) = 49 * 7 := by norm_num
      _ ≤ a * c * e := Nat.mul_le_mul nac he
  have nacf : 343 ≤ a * c * f := by
    calc (343:ℕ) = 49 * 7 := by norm_num
      _ ≤ a * c * f := Nat.mul_le_mul nac hf
  have nade : 343 ≤ a * d * e := by
    calc (343:ℕ) = 49 * 7 := by norm_num
      _ ≤ a * d * e := Nat.mul_le_mul nad he
  have nadf : 343 ≤ a * d * f := by
    calc (343:ℕ) = 49 * 7 := by norm_num
      _ ≤ a * d * f := Nat.mul_le_mul nad hf
  have naef : 343 ≤ a * e * f := by
    calc (343:ℕ) = 49 * 7 := by norm_num
      _ ≤ a * e * f := Nat.mul_le_mul nae hf
  have nbcd : 343 ≤ b * c * d := by
    calc (343:ℕ) = 49 * 7 := by norm_num
      _ ≤ b * c * d := Nat.mul_le_mul nbc hd
  have nbce : 343 ≤ b * c * e := by
    calc (343:ℕ) = 49 * 7 := by norm_num
      _ ≤ b * c * e := Nat.mul_le_mul nbc he
  have nbcf : 343 ≤ b * c * f := by
    calc (343:ℕ) = 49 * 7 := by norm_num
      _ ≤ b * c * f := Nat.mul_le_mul nbc hf
  have nbde : 343 ≤ b * d * e := by
    calc (343:ℕ) = 49 * 7 := by norm_num
      _ ≤ b * d * e := Nat.mul_le_mul nbd he
  have nbdf : 343 ≤ b * d * f := by
    calc (343:ℕ) = 49 * 7 := by norm_num
      _ ≤ b * d * f := Nat.mul_le_mul nbd hf
  have nbef : 343 ≤ b * e * f := by
    calc (343:ℕ) = 49 * 7 := by norm_num
      _ ≤ b * e * f := Nat.mul_le_mul nbe hf
  have ncde : 343 ≤ c * d * e := by
    calc (343:ℕ) = 49 * 7 := by norm_num
      _ ≤ c * d * e := Nat.mul_le_mul ncd he
  have ncdf : 343 ≤ c * d * f := by
    calc (343:ℕ) = 49 * 7 := by norm_num
      _ ≤ c * d * f := Nat.mul_le_mul ncd hf
  have ncef : 343 ≤ c * e * f := by
    calc (343:ℕ) = 49 * 7 := by norm_num
      _ ≤ c * e * f := Nat.mul_le_mul nce hf
  have ndef : 343 ≤ d * e * f := by
    calc (343:ℕ) = 49 * 7 := by norm_num
      _ ≤ d * e * f := Nat.mul_le_mul nde hf
  have nabcd : 2401 ≤ a * b * c * d := by
    calc (2401:ℕ) = 343 * 7 := by norm_num
      _ ≤ a * b * c * d := Nat.mul_le_mul nabc hd
  have nabce : 2401 ≤ a * b * c * e := by
    calc (2401:ℕ) = 343 * 7 := by norm_num
      _ ≤ a * b * c * e := Nat.mul_le_mul nabc he
  have nabcf : 2401 ≤ a * b * c * f := by
    calc (2401:ℕ) = 343 * 7 := by norm_num
      _ ≤ a * b * c * f := Nat.mul_le_mul nabc hf
  have nabde : 2401 ≤ a * b * d * e := by
    calc (2401:ℕ) = 343 * 7 := by norm_num
      _ ≤ a * b * d * e := Nat.mul_le_mul nabd he
  have nabdf : 2401 ≤ a * b * d * f := by
    calc (2401:ℕ) = 343 * 7 := by norm_num
      _ ≤ a * b * d * f := Nat.mul_le_mul nabd hf
  have nabef : 2401 ≤ a * b * e * f := by
    calc (2401:ℕ) = 343 * 7 := by norm_num
      _ ≤ a * b * e * f := Nat.mul_le_mul nabe hf
  have nacde : 2401 ≤ a * c * d * e := by
    calc (2401:ℕ) = 343 * 7 := by norm_num
      _ ≤ a * c * d * e := Nat.mul_le_mul nacd he
  have nacdf : 2401 ≤ a * c * d * f := by
    calc (2401:ℕ) = 343 * 7 := by norm_num
      _ ≤ a * c * d * f := Nat.mul_le_mul nacd hf
  have nacef : 2401 ≤ a * c * e * f := by
    calc (2401:ℕ) = 343 * 7 := by norm_num
      _ ≤ a * c * e * f := Nat.mul_le_mul nace hf
  have nadef : 2401 ≤ a * d * e * f := by
    calc (2401:ℕ) = 343 * 7 := by norm_num
      _ ≤ a * d * e * f := Nat.mul_le_mul nade hf
  have nbcde : 2401 ≤ b * c * d * e := by
    calc (2401:ℕ) = 343 * 7 := by norm_num
      _ ≤ b * c * d * e := Nat.mul_le_mul nbcd he
  have nbcdf : 2401 ≤ b * c * d * f := by
    calc (2401:ℕ) = 343 * 7 := by norm_num
      _ ≤ b * c * d * f := Nat.mul_le_mul nbcd hf
  have nbcef : 2401 ≤ b * c * e * f := by
    calc (2401:ℕ) = 343 * 7 := by norm_num
      _ ≤ b * c * e * f := Nat.mul_le_mul nbce hf
  have nbdef : 2401 ≤ b * d * e * f := by
    calc (2401:ℕ) = 343 * 7 := by norm_num
      _ ≤ b * d * e * f := Nat.mul_le_mul nbde hf
  have ncdef : 2401 ≤ c * d * e * f := by
    calc (2401:ℕ) = 343 * 7 := by norm_num
      _ ≤ c * d * e * f := Nat.mul_le_mul ncde hf
  have nabcde : 16807 ≤ a * b * c * d * e := by
    calc (16807:ℕ) = 2401 * 7 := by norm_num
      _ ≤ a * b * c * d * e := Nat.mul_le_mul nabcd he
  have nabcdf : 16807 ≤ a * b * c * d * f := by
    calc (16807:ℕ) = 2401 * 7 := by norm_num
      _ ≤ a * b * c * d * f := Nat.mul_le_mul nabcd hf
  have nabcef : 16807 ≤ a * b * c * e * f := by
    calc (16807:ℕ) = 2401 * 7 := by norm_num
      _ ≤ a * b * c * e * f := Nat.mul_le_mul nabce hf
  have nabdef : 16807 ≤ a * b * d * e * f := by
    calc (16807:ℕ) = 2401 * 7 := by norm_num
      _ ≤ a * b * d * e * f := Nat.mul_le_mul nabde hf
  have nacdef : 16807 ≤ a * c * d * e * f := by
    calc (16807:ℕ) = 2401 * 7 := by norm_num
      _ ≤ a * c * d * e * f := Nat.mul_le_mul nacde hf
  have nbcdef : 16807 ≤ b * c * d * e * f := by
    calc (16807:ℕ) = 2401 * 7 := by norm_num
      _ ≤ b * c * d * e * f := Nat.mul_le_mul nbcde hf
  have nabcdef : 117649 ≤ a * b * c * d * e * f := by
    calc (117649:ℕ) = 16807 * 7 := by norm_num
      _ ≤ a * b * c * d * e * f := Nat.mul_le_mul nabcde hf
  have Fabcde : 7 * (a * b * c * d * e) ≤ a * b * c * d * e * f := by
    calc 7 * (a * b * c * d * e) ≤ (a * b * c * d * e) * (f) := gen _ _ _ hf
      _ = a * b * c * d * e * f := by ring
  have Fabcdf : 7 * (a * b * c * d * f) ≤ a * b * c * d * e * f := by
    calc 7 * (a * b * c * d * f) ≤ (a * b * c * d * f) * (e) := gen _ _ _ he
      _ = a * b * c * d * e * f := by ring
  have Fabcef : 7 * (a * b * c * e * f) ≤ a * b * c * d * e * f := by
    calc 7 * (a * b * c * e * f) ≤ (a * b * c * e * f) * (d) := gen _ _ _ hd
      _ = a * b * c * d * e * f := by ring
  have Fabdef : 7 * (a * b * d * e * f) ≤ a * b * c * d * e * f := by
    calc 7 * (a * b * d * e * f) ≤ (a * b * d * e * f) * (c) := gen _ _ _ hc
      _ = a * b * c * d * e * f := by ring
  have Facdef : 7 * (a * c * d * e * f) ≤ a * b * c * d * e * f := by
    calc 7 * (a * c * d * e * f) ≤ (a * c * d * e * f) * (b) := gen _ _ _ hb
      _ = a * b * c * d * e * f := by ring
  have Fbcdef : 7 * (b * c * d * e * f) ≤ a * b * c * d * e * f := by
    calc 7 * (b * c * d * e * f) ≤ (b * c * d * e * f) * (a) := gen _ _ _ ha
      _ = a * b * c * d * e * f := by ring
  have Fabcd : 49 * (a * b * c * d) ≤ a * b * c * d * e * f := by
    calc 49 * (a * b * c * d) ≤ (a * b * c * d) * (e * f) := gen _ _ _ nef
      _ = a * b * c * d * e * f := by ring
  have Fabce : 49 * (a * b * c * e) ≤ a * b * c * d * e * f := by
    calc 49 * (a * b * c * e) ≤ (a * b * c * e) * (d * f) := gen _ _ _ ndf
      _ = a * b * c * d * e * f := by ring
  have Fabcf : 49 * (a * b * c * f) ≤ a * b * c * d * e * f := by
    calc 49 * (a * b * c * f) ≤ (a * b * c * f) * (d * e) := gen _ _ _ nde
      _ = a * b * c * d * e * f := by ring
  have Fabde : 49 * (a * b * d * e) ≤ a * b * c * d * e * f := by
    calc 49 * (a * b * d * e) ≤ (a * b * d * e) * (c * f) := gen _ _ _ ncf
      _ = a * b * c * d * e * f := by ring
  have Fabdf : 49 * (a * b * d * f) ≤ a * b * c * d * e * f := by
    calc 49 * (a * b * d * f) ≤ (a * b * d * f) * (c * e) := gen _ _ _ nce
      _ = a * b * c * d * e * f := by ring
  have Fabef : 49 * (a * b * e * f) ≤ a * b * c * d * e * f := by
    calc 49 * (a * b * e * f) ≤ (a * b * e * f) * (c * d) := gen _ _ _ ncd
      _ = a * b * c * d * e * f := by ring
  have Facde : 49 * (a * c * d * e) ≤ a * b * c * d * e * f := by
    calc 49 * (a * c * d * e) ≤ (a * c * d * e) * (b * f) := gen _ _ _ nbf
      _ = a * b * c * d * e * f := by ring
  have Facdf : 49 * (a * c * d * f) ≤ a * b * c * d * e * f := by
    calc 49 * (a * c * d * f) ≤ (a * c * d * f) * (b * e) := gen _ _ _ nbe
      _ = a * b * c * d * e * f := by ring
  have Facef : 49 * (a * c * e * f) ≤ a * b * c * d * e * f := by
    calc 49 * (a * c * e * f) ≤ (a * c * e * f) * (b * d) := gen _ _ _ nbd
      _ = a * b * c * d * e * f := by ring
  have Fadef : 49 * (a * d * e * f) ≤ a * b * c * d * e * f := by
    calc 49 * (a * d * e * f) ≤ (a * d * e * f) * (b * c) := gen _ _ _ nbc
      _ = a * b * c * d * e * f := by ring
  have Fbcde : 49 * (b * c * d * e) ≤ a * b * c * d * e * f := by
    calc 49 * (b * c * d * e) ≤ (b * c * d * e) * (a * f) := gen _ _ _ naf
      _ = a * b * c * d * e * f := by ring
  have Fbcdf : 49 * (b * c * d * f) ≤ a * b * c * d * e * f := by
    calc 49 * (b * c * d * f) ≤ (b * c * d * f) * (a * e) := gen _ _ _ nae
      _ = a * b * c * d * e * f := by ring
  have Fbcef : 49 * (b * c * e * f) ≤ a * b * c * d * e * f := by
    calc 49 * (b * c * e * f) ≤ (b * c * e * f) * (a * d) := gen _ _ _ nad
      _ = a * b * c * d * e * f := by ring
  have Fbdef : 49 * (b * d * e * f) ≤ a * b * c * d * e * f := by
    calc 49 * (b * d * e * f) ≤ (b * d * e * f) * (a * c) := gen _ _ _ nac
      _ = a * b * c * d * e * f := by ring
  have Fcdef : 49 * (c * d * e * f) ≤ a * b * c * d * e * f := by
    calc 49 * (c * d * e * f) ≤ (c * d * e * f) * (a * b) := gen _ _ _ nab
      _ = a * b * c * d * e * f := by ring
  have Fabc : 343 * (a * b * c) ≤ a * b * c * d * e * f := by
    calc 343 * (a * b * c) ≤ (a * b * c) * (d * e * f) := gen _ _ _ ndef
      _ = a * b * c * d * e * f := by ring
  have Fabd : 343 * (a * b * d) ≤ a * b * c * d * e * f := by
    calc 343 * (a * b * d) ≤ (a * b * d) * (c * e * f) := gen _ _ _ ncef
      _ = a * b * c * d * e * f := by ring
  have Fabe : 343 * (a * b * e) ≤ a * b * c * d * e * f := by
    calc 343 * (a * b * e) ≤ (a * b * e) * (c * d * f) := gen _ _ _ ncdf
      _ = a * b * c * d * e * f := by ring
  have Fabf : 343 * (a * b * f) ≤ a * b * c * d * e * f := by
    calc 343 * (a * b * f) ≤ (a * b * f) * (c * d * e) := gen _ _ _ ncde
      _ = a * b * c * d * e * f := by ring
  have Facd : 343 * (a * c * d) ≤ a * b * c * d * e * f := by
    calc 343 * (a * c * d) ≤ (a * c * d) * (b * e * f) := gen _ _ _ nbef
      _ = a * b * c * d * e * f := by ring
  have Face : 343 * (a * c * e) ≤ a * b * c * d * e * f := by
    calc 343 * (a * c * e) ≤ (a * c * e) * (b * d * f) := gen _ _ _ nbdf
      _ = a * b * c * d * e * f := by ring
  have Facf : 343 * (a * c * f) ≤ a * b * c * d * e * f := by
    calc 343 * (a * c * f) ≤ (a * c * f) * (b * d * e) := gen _ _ _ nbde
      _ = a * b * c * d * e * f := by ring
  have Fade : 343 * (a * d * e) ≤ a * b * c * d * e * f := by
    calc 343 * (a * d * e) ≤ (a * d * e) * (b * c * f) := gen _ _ _ nbcf
      _ = a * b * c * d * e * f := by ring
  have Fadf : 343 * (a * d * f) ≤ a * b * c * d * e * f := by
    calc 343 * (a * d * f) ≤ (a * d * f) * (b * c * e) := gen _ _ _ nbce
      _ = a * b * c * d * e * f := by ring
  have Faef : 343 * (a * e * f) ≤ a * b * c * d * e * f := by
    calc 343 * (a * e * f) ≤ (a * e * f) * (b * c * d) := gen _ _ _ nbcd
      _ = a * b * c * d * e * f := by ring
  have Fbcd : 343 * (b * c * d) ≤ a * b * c * d * e * f := by
    calc 343 * (b * c * d) ≤ (b * c * d) * (a * e * f) := gen _ _ _ naef
      _ = a * b * c * d * e * f := by ring
  have Fbce : 343 * (b * c * e) ≤ a * b * c * d * e * f := by
    calc 343 * (b * c * e) ≤ (b * c * e) * (a * d * f) := gen _ _ _ nadf
      _ = a * b * c * d * e * f := by ring
  have Fbcf : 343 * (b * c * f) ≤ a * b * c * d * e * f := by
    calc 343 * (b * c * f) ≤ (b * c * f) * (a * d * e) := gen _ _ _ nade
      _ = a * b * c * d * e * f := by ring
  have Fbde : 343 * (b * d * e) ≤ a * b * c * d * e * f := by
    calc 343 * (b * d * e) ≤ (b * d * e) * (a * c * f) := gen _ _ _ nacf
      _ = a * b * c * d * e * f := by ring
  have Fbdf : 343 * (b * d * f) ≤ a * b * c * d * e * f := by
    calc 343 * (b * d * f) ≤ (b * d * f) * (a * c * e) := gen _ _ _ nace
      _ = a * b * c * d * e * f := by ring
  have Fbef : 343 * (b * e * f) ≤ a * b * c * d * e * f := by
    calc 343 * (b * e * f) ≤ (b * e * f) * (a * c * d) := gen _ _ _ nacd
      _ = a * b * c * d * e * f := by ring
  have Fcde : 343 * (c * d * e) ≤ a * b * c * d * e * f := by
    calc 343 * (c * d * e) ≤ (c * d * e) * (a * b * f) := gen _ _ _ nabf
      _ = a * b * c * d * e * f := by ring
  have Fcdf : 343 * (c * d * f) ≤ a * b * c * d * e * f := by
    calc 343 * (c * d * f) ≤ (c * d * f) * (a * b * e) := gen _ _ _ nabe
      _ = a * b * c * d * e * f := by ring
  have Fcef : 343 * (c * e * f) ≤ a * b * c * d * e * f := by
    calc 343 * (c * e * f) ≤ (c * e * f) * (a * b * d) := gen _ _ _ nabd
      _ = a * b * c * d * e * f := by ring
  have Fdef : 343 * (d * e * f) ≤ a * b * c * d * e * f := by
    calc 343 * (d * e * f) ≤ (d * e * f) * (a * b * c) := gen _ _ _ nabc
      _ = a * b * c * d * e * f := by ring
  have Fab : 2401 * (a * b) ≤ a * b * c * d * e * f := by
    calc 2401 * (a * b) ≤ (a * b) * (c * d * e * f) := gen _ _ _ ncdef
      _ = a * b * c * d * e * f := by ring
  have Fac : 2401 * (a * c) ≤ a * b * c * d * e * f := by
    calc 2401 * (a * c) ≤ (a * c) * (b * d * e * f) := gen _ _ _ nbdef
      _ = a * b * c * d * e * f := by ring
  have Fad : 2401 * (a * d) ≤ a * b * c * d * e * f := by
    calc 2401 * (a * d) ≤ (a * d) * (b * c * e * f) := gen _ _ _ nbcef
      _ = a * b * c * d * e * f := by ring
  have Fae : 2401 * (a * e) ≤ a * b * c * d * e * f := by
    calc 2401 * (a * e) ≤ (a * e) * (b * c * d * f) := gen _ _ _ nbcdf
      _ = a * b * c * d * e * f := by ring
  have Faf : 2401 * (a * f) ≤ a * b * c * d * e * f := by
    calc 2401 * (a * f) ≤ (a * f) * (b * c * d * e) := gen _ _ _ nbcde
      _ = a * b * c * d * e * f := by ring
  have Fbc : 2401 * (b * c) ≤ a * b * c * d * e * f := by
    calc 2401 * (b * c) ≤ (b * c) * (a * d * e * f) := gen _ _ _ nadef
      _ = a * b * c * d * e * f := by ring
  have Fbd : 2401 * (b * d) ≤ a * b * c * d * e * f := by
    calc 2401 * (b * d) ≤ (b * d) * (a * c * e * f) := gen _ _ _ nacef
      _ = a * b * c * d * e * f := by ring
  have Fbe : 2401 * (b * e) ≤ a * b * c * d * e * f := by
    calc 2401 * (b * e) ≤ (b * e) * (a * c * d * f) := gen _ _ _ nacdf
      _ = a * b * c * d * e * f := by ring
  have Fbf : 2401 * (b * f) ≤ a * b * c * d * e * f := by
    calc 2401 * (b * f) ≤ (b * f) * (a * c * d * e) := gen _ _ _ nacde
      _ = a * b * c * d * e * f := by ring
  have Fcd : 2401 * (c * d) ≤ a * b * c * d * e * f := by
    calc 2401 * (c * d) ≤ (c * d) * (a * b * e * f) := gen _ _ _ nabef
      _ = a * b * c * d * e * f := by ring
  have Fce : 2401 * (c * e) ≤ a * b * c * d * e * f := by
    calc 2401 * (c * e) ≤ (c * e) * (a * b * d * f) := gen _ _ _ nabdf
      _ = a * b * c * d * e * f := by ring
  have Fcf : 2401 * (c * f) ≤ a * b * c * d * e * f := by
    calc 2401 * (c * f) ≤ (c * f) * (a * b * d * e) := gen _ _ _ nabde
      _ = a * b * c * d * e * f := by ring
  have Fde : 2401 * (d * e) ≤ a * b * c * d * e * f := by
    calc 2401 * (d * e) ≤ (d * e) * (a * b * c * f) := gen _ _ _ nabcf
      _ = a * b * c * d * e * f := by ring
  have Fdf : 2401 * (d * f) ≤ a * b * c * d * e * f := by
    calc 2401 * (d * f) ≤ (d * f) * (a * b * c * e) := gen _ _ _ nabce
      _ = a * b * c * d * e * f := by ring
  have Fef : 2401 * (e * f) ≤ a * b * c * d * e * f := by
    calc 2401 * (e * f) ≤ (e * f) * (a * b * c * d) := gen _ _ _ nabcd
      _ = a * b * c * d * e * f := by ring
  have Fa : 16807 * (a) ≤ a * b * c * d * e * f := by
    calc 16807 * (a) ≤ (a) * (b * c * d * e * f) := gen _ _ _ nbcdef
      _ = a * b * c * d * e * f := by ring
  have Fb : 16807 * (b) ≤ a * b * c * d * e * f := by
    calc 16807 * (b) ≤ (b) * (a * c * d * e * f) := gen _ _ _ nacdef
      _ = a * b * c * d * e * f := by ring
  have Fc : 16807 * (c) ≤ a * b * c * d * e * f := by
    calc 16807 * (c) ≤ (c) * (a * b * d * e * f) := gen _ _ _ nabdef
      _ = a * b * c * d * e * f := by ring
  have Fd : 16807 * (d) ≤ a * b * c * d * e * f := by
    calc 16807 * (d) ≤ (d) * (a * b * c * e * f) := gen _ _ _ nabcef
      _ = a * b * c * d * e * f := by ring
  have Fe : 16807 * (e) ≤ a * b * c * d * e * f := by
    calc 16807 * (e) ≤ (e) * (a * b * c * d * f) := gen _ _ _ nabcdf
      _ = a * b * c * d * e * f := by ring
  have Ff : 16807 * (f) ≤ a * b * c * d * e * f := by
    calc 16807 * (f) ≤ (f) * (a * b * c * d * e) := gen _ _ _ nabcde
      _ = a * b * c * d * e * f := by ring
  have F0 : 117649 ≤ a * b * c * d * e * f := nabcdef
  obtain ⟨Pv, dP⟩ : ∃ p, a * b * c * d * e * f = p := ⟨_, rfl⟩
  obtain ⟨E5, d5⟩ : ∃ q, a * b * c * d * e + a * b * c * d * f + a * b * c * e * f + a * b * d * e * f + a * c * d * e * f + b * c * d * e * f = q := ⟨_, rfl⟩
  obtain ⟨E4, d4⟩ : ∃ q, a * b * c * d + a * b * c * e + a * b * c * f + a * b * d * e + a * b * d * f + a * b * e * f + a * c * d * e + a * c * d * f + a * c * e * f + a * d * e * f + b * c * d * e + b * c * d * f + b * c * e * f + b * d * e * f + c * d * e * f = q := ⟨_, rfl⟩
  obtain ⟨E3, d3⟩ : ∃ q, a * b * c + a * b * d + a * b * e + a * b * f + a * c * d + a * c * e + a * c * f + a * d * e + a * d * f + a * e * f + b * c * d + b * c * e + b * c * f + b * d * e + b * d * f + b * e * f + c * d * e + c * d * f + c * e * f + d * e * f = q := ⟨_, rfl⟩
  obtain ⟨E2, d2⟩ : ∃ q, a * b + a * c + a * d + a * e + a * f + b * c + b * d + b * e + b * f + c * d + c * e + c * f + d * e + d * f + e * f = q := ⟨_, rfl⟩
  obtain ⟨E1, d1⟩ : ∃ q, a + b + c + d + e + f = q := ⟨_, rfl⟩
  have A5 : 7 * E5 ≤ 6 * Pv := by
    rw [← d5, ← dP]; linarith only [Fabcde, Fabcdf, Fabcef, Fabdef, Facdef, Fbcdef]
  have A4 : 49 * E4 ≤ 15 * Pv := by
    rw [← d4, ← dP]; linarith only [Fabcd, Fabce, Fabcf, Fabde, Fabdf, Fabef, Facde, Facdf, Facef, Fadef, Fbcde, Fbcdf, Fbcef, Fbdef, Fcdef]
  have A3 : 343 * E3 ≤ 20 * Pv := by
    rw [← d3, ← dP]; linarith only [Fabc, Fabd, Fabe, Fabf, Facd, Face, Facf, Fade, Fadf, Faef, Fbcd, Fbce, Fbcf, Fbde, Fbdf, Fbef, Fcde, Fcdf, Fcef, Fdef]
  have A2 : 2401 * E2 ≤ 15 * Pv := by
    rw [← d2, ← dP]; linarith only [Fab, Fac, Fad, Fae, Faf, Fbc, Fbd, Fbe, Fbf, Fcd, Fce, Fcf, Fde, Fdf, Fef]
  have A1 : 16807 * E1 ≤ 6 * Pv := by
    rw [← d1, ← dP]; linarith only [Fa, Fb, Fc, Fd, Fe, Ff]
  rw [dP] at F0
  rw [d5, d4, d3, d2, d1, dP]
  omega

set_option maxHeartbeats 1000000 in
theorem solution (m : ℕ) (hm : 0 < m) (hcyc : syracuseStep^[6] m = m) : m = 1 := by
  have hc : syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (m)))))) = m := by
    have h : syracuseStep^[6] m = syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (m)))))) := by
      simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq]
    rwa [h] at hcyc
  obtain ⟨x1, hx1⟩ : ∃ y, syracuseStep m = y := ⟨_, rfl⟩
  obtain ⟨x2, hx2⟩ : ∃ y, syracuseStep x1 = y := ⟨_, rfl⟩
  obtain ⟨x3, hx3⟩ : ∃ y, syracuseStep x2 = y := ⟨_, rfl⟩
  obtain ⟨x4, hx4⟩ : ∃ y, syracuseStep x3 = y := ⟨_, rfl⟩
  obtain ⟨x5, hx5⟩ : ∃ y, syracuseStep x4 = y := ⟨_, rfl⟩
  rw [hx1, hx2, hx3, hx4, hx5] at hc
  have p1 : 0 < x1 := hx1 ▸ stepPos
  have p2 : 0 < x2 := hx2 ▸ stepPos
  have p3 : 0 < x3 := hx3 ▸ stepPos
  have p4 : 0 < x4 := hx4 ▸ stepPos
  have p5 : 0 < x5 := hx5 ▸ stepPos
  have o0 : Odd m := hc ▸ stepOdd x5
  have o1 : Odd x1 := hx1 ▸ stepOdd m
  have o2 : Odd x2 := hx2 ▸ stepOdd x1
  have o3 : Odd x3 := hx3 ▸ stepOdd x2
  have o4 : Odd x4 := hx4 ▸ stepOdd x3
  have o5 : Odd x5 := hx5 ▸ stepOdd x4
  obtain ⟨c0, e0⟩ : ∃ q, 2 ^ q * x1 = 3 * m + 1 := ⟨_, hx1 ▸ stepSplit m⟩
  obtain ⟨c1, e1⟩ : ∃ q, 2 ^ q * x2 = 3 * x1 + 1 := ⟨_, hx2 ▸ stepSplit x1⟩
  obtain ⟨c2, e2⟩ : ∃ q, 2 ^ q * x3 = 3 * x2 + 1 := ⟨_, hx3 ▸ stepSplit x2⟩
  obtain ⟨c3, e3⟩ : ∃ q, 2 ^ q * x4 = 3 * x3 + 1 := ⟨_, hx4 ▸ stepSplit x3⟩
  obtain ⟨c4, e4⟩ : ∃ q, 2 ^ q * x5 = 3 * x4 + 1 := ⟨_, hx5 ▸ stepSplit x4⟩
  obtain ⟨c5, e5⟩ : ∃ q, 2 ^ q * m = 3 * x5 + 1 := ⟨_, hc ▸ stepSplit x5⟩
  have hP : 0 < m * x1 * x2 * x3 * x4 * x5 := by positivity
  have hprod : 2 ^ (c0 + c1 + c2 + c3 + c4 + c5) * (m * x1 * x2 * x3 * x4 * x5) = 729 * (m * x1 * x2 * x3 * x4 * x5)
        + 243 * (m * x1 * x2 * x3 * x4 + m * x1 * x2 * x3 * x5 + m * x1 * x2 * x4 * x5 + m * x1 * x3 * x4 * x5 + m * x2 * x3 * x4 * x5 + x1 * x2 * x3 * x4 * x5)
        + 81 * (m * x1 * x2 * x3 + m * x1 * x2 * x4 + m * x1 * x2 * x5 + m * x1 * x3 * x4 + m * x1 * x3 * x5 + m * x1 * x4 * x5 + m * x2 * x3 * x4 + m * x2 * x3 * x5 + m * x2 * x4 * x5 + m * x3 * x4 * x5 + x1 * x2 * x3 * x4 + x1 * x2 * x3 * x5 + x1 * x2 * x4 * x5 + x1 * x3 * x4 * x5 + x2 * x3 * x4 * x5)
        + 27 * (m * x1 * x2 + m * x1 * x3 + m * x1 * x4 + m * x1 * x5 + m * x2 * x3 + m * x2 * x4 + m * x2 * x5 + m * x3 * x4 + m * x3 * x5 + m * x4 * x5 + x1 * x2 * x3 + x1 * x2 * x4 + x1 * x2 * x5 + x1 * x3 * x4 + x1 * x3 * x5 + x1 * x4 * x5 + x2 * x3 * x4 + x2 * x3 * x5 + x2 * x4 * x5 + x3 * x4 * x5)
        + 9 * (m * x1 + m * x2 + m * x3 + m * x4 + m * x5 + x1 * x2 + x1 * x3 + x1 * x4 + x1 * x5 + x2 * x3 + x2 * x4 + x2 * x5 + x3 * x4 + x3 * x5 + x4 * x5)
        + 3 * (m + x1 + x2 + x3 + x4 + x5)
        + 1 := by
    rw [pow_add, pow_add, pow_add, pow_add, pow_add]
    calc 2 ^ c0 * 2 ^ c1 * 2 ^ c2 * 2 ^ c3 * 2 ^ c4 * 2 ^ c5 * (m * x1 * x2 * x3 * x4 * x5)
        = (2 ^ c0 * x1) * (2 ^ c1 * x2) * (2 ^ c2 * x3) * (2 ^ c3 * x4) * (2 ^ c4 * x5) * (2 ^ c5 * m) := by ring
      _ = (3 * m + 1) * (3 * x1 + 1) * (3 * x2 + 1) * (3 * x3 + 1) * (3 * x4 + 1) * (3 * x5 + 1) := by rw [e0, e1, e2, e3, e4, e5]
      _ = _ := by ring
  have hlow : 729 < 2 ^ (c0 + c1 + c2 + c3 + c4 + c5) := by
    by_contra hcon
    push Not at hcon
    have hle := Nat.mul_le_mul_right (m * x1 * x2 * x3 * x4 * x5) hcon
    rw [hprod] at hle
    omega
  have hhigh : 1024 ≤ 2 ^ (c0 + c1 + c2 + c3 + c4 + c5) := by
    by_contra hcon
    push Not at hcon
    have hk : c0 + c1 + c2 + c3 + c4 + c5 ≤ 9 := by
      by_contra hkk
      push Not at hkk
      have h8 : (2:ℕ) ^ 10 ≤ 2 ^ (c0 + c1 + c2 + c3 + c4 + c5) := Nat.pow_le_pow_right (by norm_num) (by omega)
      norm_num at h8; omega
    have h7 : (2:ℕ) ^ (c0 + c1 + c2 + c3 + c4 + c5) ≤ 2 ^ 9 := Nat.pow_le_pow_right (by norm_num) hk
    norm_num at h7; omega
  have hkey : 295 * (m * x1 * x2 * x3 * x4 * x5) ≤ 243 * (m * x1 * x2 * x3 * x4 + m * x1 * x2 * x3 * x5 + m * x1 * x2 * x4 * x5 + m * x1 * x3 * x4 * x5 + m * x2 * x3 * x4 * x5 + x1 * x2 * x3 * x4 * x5)
        + 81 * (m * x1 * x2 * x3 + m * x1 * x2 * x4 + m * x1 * x2 * x5 + m * x1 * x3 * x4 + m * x1 * x3 * x5 + m * x1 * x4 * x5 + m * x2 * x3 * x4 + m * x2 * x3 * x5 + m * x2 * x4 * x5 + m * x3 * x4 * x5 + x1 * x2 * x3 * x4 + x1 * x2 * x3 * x5 + x1 * x2 * x4 * x5 + x1 * x3 * x4 * x5 + x2 * x3 * x4 * x5)
        + 27 * (m * x1 * x2 + m * x1 * x3 + m * x1 * x4 + m * x1 * x5 + m * x2 * x3 + m * x2 * x4 + m * x2 * x5 + m * x3 * x4 + m * x3 * x5 + m * x4 * x5 + x1 * x2 * x3 + x1 * x2 * x4 + x1 * x2 * x5 + x1 * x3 * x4 + x1 * x3 * x5 + x1 * x4 * x5 + x2 * x3 * x4 + x2 * x3 * x5 + x2 * x4 * x5 + x3 * x4 * x5)
        + 9 * (m * x1 + m * x2 + m * x3 + m * x4 + m * x5 + x1 * x2 + x1 * x3 + x1 * x4 + x1 * x5 + x2 * x3 + x2 * x4 + x2 * x5 + x3 * x4 + x3 * x5 + x4 * x5)
        + 3 * (m + x1 + x2 + x3 + x4 + x5)
        + 1 := by
    have h1 := Nat.mul_le_mul_right (m * x1 * x2 * x3 * x4 * x5) hhigh
    rw [hprod] at h1
    omega
  have hsmall : m < 7 ∨ x1 < 7 ∨ x2 < 7 ∨ x3 < 7 ∨ x4 < 7 ∨ x5 < 7 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2, g3, g4, g5⟩ := hcon
    exact absurd hkey (not_le.mpr (six_bound m x1 x2 x3 x4 x5 g0 g1 g2 g3 g4 g5))
  rcases hsmall with h | h | h | h | h | h
  · have hper : syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (m)))))) = m := by rw [hx1, hx2, hx3, hx4, hx5, hc]
    have h1 : m = 1 := syracuse_no_small_cycle m 6 hm (by norm_num) (by omega) (by
      show syracuseStep^[6] m = m
      simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq]
      exact hper)
    exact h1
  · have hper : syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (x1)))))) = x1 := by rw [hx2, hx3, hx4, hx5, hc, hx1]
    have h1 : x1 = 1 := syracuse_no_small_cycle x1 6 p1 (by norm_num) (by omega) (by
      show syracuseStep^[6] x1 = x1
      simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq]
      exact hper)
    have q2 : x2 = 1 := by rw [← hx2, h1, T1]
    have q3 : x3 = 1 := by rw [← hx3, q2, T1]
    have q4 : x4 = 1 := by rw [← hx4, q3, T1]
    have q5 : x5 = 1 := by rw [← hx5, q4, T1]
    rw [q5, T1] at hc; omega
  · have hper : syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (x2)))))) = x2 := by rw [hx3, hx4, hx5, hc, hx1, hx2]
    have h1 : x2 = 1 := syracuse_no_small_cycle x2 6 p2 (by norm_num) (by omega) (by
      show syracuseStep^[6] x2 = x2
      simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq]
      exact hper)
    have q3 : x3 = 1 := by rw [← hx3, h1, T1]
    have q4 : x4 = 1 := by rw [← hx4, q3, T1]
    have q5 : x5 = 1 := by rw [← hx5, q4, T1]
    rw [q5, T1] at hc; omega
  · have hper : syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (x3)))))) = x3 := by rw [hx4, hx5, hc, hx1, hx2, hx3]
    have h1 : x3 = 1 := syracuse_no_small_cycle x3 6 p3 (by norm_num) (by omega) (by
      show syracuseStep^[6] x3 = x3
      simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq]
      exact hper)
    have q4 : x4 = 1 := by rw [← hx4, h1, T1]
    have q5 : x5 = 1 := by rw [← hx5, q4, T1]
    rw [q5, T1] at hc; omega
  · have hper : syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (x4)))))) = x4 := by rw [hx5, hc, hx1, hx2, hx3, hx4]
    have h1 : x4 = 1 := syracuse_no_small_cycle x4 6 p4 (by norm_num) (by omega) (by
      show syracuseStep^[6] x4 = x4
      simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq]
      exact hper)
    have q5 : x5 = 1 := by rw [← hx5, h1, T1]
    rw [q5, T1] at hc; omega
  · have hper : syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (syracuseStep (x5)))))) = x5 := by rw [hc, hx1, hx2, hx3, hx4, hx5]
    have h1 : x5 = 1 := syracuse_no_small_cycle x5 6 p5 (by norm_num) (by omega) (by
      show syracuseStep^[6] x5 = x5
      simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq]
      exact hper)
    rw [h1, T1] at hc; omega
