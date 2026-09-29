-- Prove2me | solution 1 for mme_floor_behrend_polynomial_loss_ge_exp_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T17:40:51.756583+00:00
-- url     : https://prove2.me/submissions/1170b37b-9b19-4698-8900-944f36e7cfed

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic
import Theorems.Thm_mme_nat_div_real_half_lower

open Filter Topology

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (n p : ℕ) (D A B : ℝ)
    (hA : 0 ≤ A)
    (hp : 2 ≤ p)
    (hpUpper : (p : ℝ) ≤
      Real.exp (A * (((n + 1 : ℕ) : ℝ))))
    (hDpos : 0 < D)
    (hDUpper : D ≤
      Real.exp (B * Real.sqrt (((n + 1 : ℕ) : ℝ)))) :
    Real.exp
        (-(4 + 4 * (A + 1) + B) *
          Real.sqrt (((n + 1 : ℕ) : ℝ))) ≤
      ((((p / 2 : ℕ) : ℝ) / (p : ℝ)) *
          Real.exp
            (-4 * Real.sqrt
              (Real.log (((p / 2 : ℕ) : ℝ))))) /
        D := by
  let y : ℝ := (((n + 1 : ℕ) : ℝ))
  let x : ℝ := Real.sqrt y
  have hy : 1 ≤ y := by
    dsimp only [y]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hy0 : 0 ≤ y := hy.trans' (by norm_num)
  have hx0 : 0 ≤ x := by
    dsimp only [x]
    positivity
  have hx1 : 1 ≤ x := by
    dsimp only [x]
    calc
      (1 : ℝ) = Real.sqrt 1 := by norm_num
      _ ≤ Real.sqrt y := Real.sqrt_le_sqrt hy
  have hx2 : x ^ 2 = y := by
    dsimp only [x]
    exact Real.sq_sqrt hy0

  have hpNat : 0 < p := by omega
  have hpReal : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpNat
  have hhalfNat : 0 < p / 2 := Nat.div_pos hp (by omega)
  have hhalfReal : (0 : ℝ) < ((p / 2 : ℕ) : ℝ) := by
    exact_mod_cast hhalfNat
  have hhalfLeNat : p / 2 ≤ p := Nat.div_le_self p 2
  have hhalfLe : (((p / 2 : ℕ) : ℝ)) ≤ (p : ℝ) := by
    exact_mod_cast hhalfLeNat

  have hlogP : Real.log (p : ℝ) ≤ A * y := by
    exact (Real.log_le_iff_le_exp hpReal).2 (by simpa only [y] using hpUpper)
  have hlogHalf :
      Real.log (((p / 2 : ℕ) : ℝ)) ≤ A * y := by
    exact (Real.log_le_log hhalfReal hhalfLe).trans hlogP
  have hlogHalf0 : 0 ≤ Real.log (((p / 2 : ℕ) : ℝ)) := by
    exact Real.log_nonneg (by exact_mod_cast hhalfNat)
  have hAy0 : 0 ≤ A * y := mul_nonneg hA hy0
  have hsqrtLog :
      Real.sqrt (Real.log (((p / 2 : ℕ) : ℝ))) ≤ (A + 1) * x := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · rw [mul_pow, hx2]
      have hAquad : A ≤ (A + 1) ^ 2 := by nlinarith [sq_nonneg A]
      exact hlogHalf.trans
        (mul_le_mul_of_nonneg_right hAquad hy0)
  have hbehrend :
      Real.exp (-4 * (A + 1) * x) ≤
        Real.exp
          (-4 * Real.sqrt
            (Real.log (((p / 2 : ℕ) : ℝ)))) := by
    apply Real.exp_le_exp.mpr
    nlinarith

  have hfloorRaw := mme_nat_div_real_half_lower
    (n := p) (d := 2) (by omega) hp
  have hfloor :
      (1 / 4 : ℝ) ≤ (((p / 2 : ℕ) : ℝ)) / (p : ℝ) := by
    apply (le_div_iff₀ hpReal).2
    nlinarith

  have hconst : Real.exp (-4 * x) ≤ (1 / 4 : ℝ) := by
    have hexpFour : (4 : ℝ) ≤ Real.exp 4 := by
      linarith [Real.add_one_le_exp (4 : ℝ)]
    have hnegFour : Real.exp (-4) ≤ (1 / 4 : ℝ) := by
      rw [Real.exp_neg]
      simpa only [one_div] using
        (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4) hexpFour)
    exact (Real.exp_le_exp.mpr (by nlinarith)).trans hnegFour

  have hDrecip : Real.exp (-B * x) ≤ D⁻¹ := by
    rw [show -B * x = -(B * x) by ring, Real.exp_neg]
    exact inv_anti₀ hDpos (by simpa only [x] using hDUpper)

  change Real.exp (-(4 + 4 * (A + 1) + B) * x) ≤
    ((((p / 2 : ℕ) : ℝ) / (p : ℝ)) *
      Real.exp (-4 * Real.sqrt
        (Real.log (((p / 2 : ℕ) : ℝ))))) / D
  rw [div_eq_mul_inv]
  calc
    Real.exp (-(4 + 4 * (A + 1) + B) * x) =
        Real.exp (-4 * x) *
          Real.exp (-4 * (A + 1) * x) *
            Real.exp (-B * x) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ (1 / 4 : ℝ) *
          Real.exp (-4 * Real.sqrt
            (Real.log (((p / 2 : ℕ) : ℝ)))) * D⁻¹ := by
      gcongr
    _ ≤ (((p / 2 : ℕ) : ℝ) / (p : ℝ)) *
          Real.exp (-4 * Real.sqrt
            (Real.log (((p / 2 : ℕ) : ℝ)))) * D⁻¹ := by
      gcongr
