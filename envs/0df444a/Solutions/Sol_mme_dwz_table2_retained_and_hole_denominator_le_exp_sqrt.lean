-- Prove2me | solution 1 for mme_dwz_table2_retained_and_hole_denominator_le_exp_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T18:29:03.431413+00:00
-- url     : https://prove2.me/submissions/573096fb-28e7-450b-ad72-6512db717dc0

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

theorem solution (L : ℕ) :
    let x : ℝ := (((L + 1 : ℕ) : ℝ))
    let jointPoly : ℝ := (6 * x) ^ 15
    let degreePoly : ℝ := (6 * x) ^ 5 * x ^ 15
    let zPoly : ℝ := (6 * x) ^ 5
    let compatibilityPoly : ℝ := (6 * x) ^ 9
    let B : ℝ := 32 * 6 ^ 20 * ((70 : ℕ).factorial : ℝ)
    (32 * max (jointPoly * degreePoly) (zPoly * compatibilityPoly)) *
        (16 * (((4 * L + 1 : ℕ) : ℝ))) ≤
      Real.exp (B * Real.sqrt x) := by
  dsimp only
  let x : ℝ := (((L + 1 : ℕ) : ℝ))
  let y : ℝ := Real.sqrt x
  let B : ℝ := 32 * 6 ^ 20 * ((70 : ℕ).factorial : ℝ)
  have hx1 : (1 : ℝ) ≤ x := by
    dsimp only [x]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le L)
  have hx0 : 0 ≤ x := hx1.trans' (by norm_num)
  have hy0 : 0 ≤ y := by dsimp only [y]; positivity
  have hy2 : y ^ 2 = x := by
    dsimp only [y]
    exact Real.sq_sqrt hx0
  have hy72 : y ^ 72 = x ^ 36 := by
    calc
      y ^ 72 = (y ^ 2) ^ 36 := by norm_num [← pow_mul]
      _ = x ^ 36 := by rw [hy2]
  have hx21 : (1 : ℝ) ≤ x ^ 21 := one_le_pow₀ hx1
  have h6six : (1 : ℝ) ≤ (6 : ℝ) ^ 6 := one_le_pow₀ (by norm_num)
  have hfactor : (1 : ℝ) ≤ 6 ^ 6 * x ^ 21 :=
    one_le_mul_of_one_le_of_one_le h6six hx21
  have hsmallNonneg : (0 : ℝ) ≤ 6 ^ 14 * x ^ 14 := by positivity
  have hbranch : (6 * x) ^ 5 * (6 * x) ^ 9 ≤
      (6 * x) ^ 15 * ((6 * x) ^ 5 * x ^ 15) := by
    calc
      (6 * x) ^ 5 * (6 * x) ^ 9 = 6 ^ 14 * x ^ 14 := by ring
      _ ≤ (6 ^ 14 * x ^ 14) * (6 ^ 6 * x ^ 21) :=
        le_mul_of_one_le_right hsmallNonneg hfactor
      _ = (6 * x) ^ 15 * ((6 * x) ^ 5 * x ^ 15) := by ring
  rw [max_eq_left hbranch]
  have hgroup : (((4 * L + 1 : ℕ) : ℝ)) ≤ 4 * x := by
    dsimp only [x]
    push_cast
    linarith
  have hB0 : 0 ≤ B := by dsimp only [B]; positivity
  have hcoeff :
      (2048 : ℝ) * 6 ^ 20 * ((72 : ℕ).factorial : ℝ) ≤ B ^ 72 := by
    dsimp only [B]
    norm_num [Nat.factorial]
  have hpoly :
      ((2048 : ℝ) * 6 ^ 20 * x ^ 36) *
          ((72 : ℕ).factorial : ℝ) ≤ (B * y) ^ 72 := by
    rw [mul_pow, hy72]
    calc
      ((2048 : ℝ) * 6 ^ 20 * x ^ 36) *
            ((72 : ℕ).factorial : ℝ) =
          ((2048 : ℝ) * 6 ^ 20 * ((72 : ℕ).factorial : ℝ)) *
            x ^ 36 := by ring
      _ ≤ B ^ 72 * x ^ 36 := by gcongr
  calc
    (32 * ((6 * x) ^ 15 * ((6 * x) ^ 5 * x ^ 15))) *
          (16 * (((4 * L + 1 : ℕ) : ℝ))) ≤
        (32 * ((6 * x) ^ 15 * ((6 * x) ^ 5 * x ^ 15))) *
          (16 * (4 * x)) := by gcongr
    _ = (2048 : ℝ) * 6 ^ 20 * x ^ 36 := by ring
    _ ≤ (B * y) ^ 72 / ((72 : ℕ).factorial : ℝ) := by
      apply (le_div_iff₀ (by positivity :
        (0 : ℝ) < ((72 : ℕ).factorial : ℝ))).2
      simpa only [mul_assoc] using hpoly
    _ ≤ Real.exp (B * y) :=
      Real.pow_div_factorial_le_exp (B * y) (mul_nonneg hB0 hy0) 72
    _ = Real.exp (B * Real.sqrt x) := by rfl
