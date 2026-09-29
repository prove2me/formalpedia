-- Prove2me | solution 1 for mme_CW_q6_floor_rate_absorption
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T03:39:23.841184+00:00
-- url     : https://prove2.me/submissions/baabf1bd-de69-4e4b-86b7-6324161843a5

import Mathlib
import Theorems.Thm_mme_nat_div_real_half_lower

open Filter Topology

set_option autoImplicit false

private lemma exp_add_log32_sqrt_le_div
    {C r : ℝ} (hC : 0 ≤ C) (hr : 1 ≤ r) :
    Real.exp (-(C + Real.log 32) * r) ≤
      Real.exp (-C * r) / 32 := by
  have hlog : 0 ≤ Real.log (32 : ℝ) := Real.log_nonneg (by norm_num)
  have hlogmul : -(Real.log 32) * r ≤ -Real.log 32 := by
    nlinarith
  have hexpLog :
      Real.exp (-(Real.log 32) * r) ≤ (1 : ℝ) / 32 := by
    calc
      Real.exp (-(Real.log 32) * r) ≤ Real.exp (-Real.log 32) :=
        Real.exp_le_exp.mpr hlogmul
      _ = (1 : ℝ) / 32 := by
        rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 32)]
        norm_num
  rw [show -(C + Real.log 32) * r = -C * r + (-(Real.log 32) * r) by ring,
    Real.exp_add]
  calc
    Real.exp (-C * r) * Real.exp (-(Real.log 32) * r)
        ≤ Real.exp (-C * r) * ((1 : ℝ) / 32) := by
          gcongr
    _ = Real.exp (-C * r) / 32 := by ring

private lemma exp_add_log32_sqrt_le_one_div
    {C r : ℝ} (hC : 0 ≤ C) (hr : 1 ≤ r) :
    Real.exp (-(C + Real.log 32) * r) ≤ (1 : ℝ) / 32 := by
  calc
    Real.exp (-(C + Real.log 32) * r)
        ≤ Real.exp (-C * r) / 32 := exp_add_log32_sqrt_le_div hC hr
    _ ≤ 1 / 32 := by
      gcongr
      rw [Real.exp_le_one_iff]
      nlinarith

theorem q6_A_rate_absorption
    {N S Z M A : ℕ} {C : ℝ}
    (hC : 0 ≤ C)
    (hM : 0 < M)
    (hMZ : M ≤ 5 * Z)
    (hS : 80 ≤ S)
    (hA : (S * Z) / (16 * M) ≤ A)
    (hdensity :
      Real.exp (-C * Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
        (S : ℝ) / (M : ℝ) / (((N + 1 : ℕ) : ℝ)) ) :
    (Z : ℝ) *
        Real.exp (-(C + Real.log 32) *
          Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
      (A : ℝ) := by
  let r : ℝ := Real.sqrt (((N + 1 : ℕ) : ℝ))
  have hr : 1 ≤ r := by
    dsimp [r]
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le N)))
  have hdenN : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.succ_le_succ (Nat.zero_le N))
  have hdensity' : Real.exp (-C * r) ≤ (S : ℝ) / (M : ℝ) := by
    calc
      Real.exp (-C * r) ≤
          (S : ℝ) / (M : ℝ) / (((N + 1 : ℕ) : ℝ)) := hdensity
      _ ≤ (S : ℝ) / (M : ℝ) := by
        exact div_le_self (by positivity) hdenN
  have hSM : 16 * M ≤ S * Z := by
    calc
      16 * M ≤ 16 * (5 * Z) := Nat.mul_le_mul_left 16 hMZ
      _ = 80 * Z := by ring
      _ ≤ S * Z := Nat.mul_le_mul_right Z hS
  have hfloor := mme_nat_div_real_half_lower
    (n := S * Z) (d := 16 * M) (by positivity) hSM
  have hrate :
      (Z : ℝ) * Real.exp (-(C + Real.log 32) * r) ≤
        ((S * Z : ℕ) : ℝ) / (2 * ((16 * M : ℕ) : ℝ)) := by
    calc
      (Z : ℝ) * Real.exp (-(C + Real.log 32) * r)
          ≤ (Z : ℝ) * (Real.exp (-C * r) / 32) := by
            gcongr
            exact exp_add_log32_sqrt_le_div hC hr
      _ ≤ (Z : ℝ) * (((S : ℝ) / (M : ℝ)) / 32) := by
            gcongr
      _ = ((S * Z : ℕ) : ℝ) / (2 * ((16 * M : ℕ) : ℝ)) := by
            push_cast
            field_simp
            ring
  exact hrate.trans (hfloor.trans (by exact_mod_cast hA))

theorem q6_H_rate_absorption
    {N X B M H : ℕ} {C : ℝ}
    (hC : 0 ≤ C)
    (hX : 0 < X)
    (hM : M = 4 * X ^ 2 + 1)
    (hlarge : 400 * M ≤ B)
    (hH : H = B / (8 * M)) :
    (B : ℝ) *
        Real.exp (-(C + Real.log 32) *
          Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
      4 * (X : ℝ) ^ 2 * (H : ℝ) := by
  let r : ℝ := Real.sqrt (((N + 1 : ℕ) : ℝ))
  have hr : 1 ≤ r := by
    dsimp [r]
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le N)))
  have hMpos : 0 < M := by omega
  have h8M : 8 * M ≤ B := by omega
  have hfloor := mme_nat_div_real_half_lower
    (n := B) (d := 8 * M) (by positivity) h8M
  have hM8X : M ≤ 8 * X ^ 2 := by
    rw [hM]
    have : 1 ≤ X ^ 2 := by nlinarith
    omega
  have hbase : (B : ℝ) / 32 ≤
      4 * (X : ℝ) ^ 2 * ((B : ℝ) / (2 * ((8 * M : ℕ) : ℝ))) := by
    have hM8XR : (M : ℝ) ≤ 8 * (X : ℝ) ^ 2 := by exact_mod_cast hM8X
    have hMposR : 0 < (M : ℝ) := by exact_mod_cast hMpos
    have hBnonneg : 0 ≤ (B : ℝ) := by positivity
    push_cast
    rw [div_eq_mul_inv]
    field_simp
    nlinarith
  calc
    (B : ℝ) * Real.exp (-(C + Real.log 32) * r)
        ≤ (B : ℝ) * ((1 : ℝ) / 32) := by
          gcongr
          exact exp_add_log32_sqrt_le_one_div hC hr
    _ = (B : ℝ) / 32 := by ring
    _ ≤ 4 * (X : ℝ) ^ 2 * ((B : ℝ) / (2 * ((8 * M : ℕ) : ℝ))) := hbase
    _ ≤ 4 * (X : ℝ) ^ 2 * (H : ℝ) := by
      rw [hH]
      gcongr

theorem solution
    {N S Z X B M A H : ℕ} {C : ℝ}
    (hC : 0 ≤ C)
    (hX : 0 < X)
    (hM : M = 4 * X ^ 2 + 1)
    (hMZ : M ≤ 5 * Z)
    (hS : 80 ≤ S)
    (hA : (S * Z) / (16 * M) ≤ A)
    (hlarge : 400 * M ≤ B)
    (hH : H = B / (8 * M))
    (hdensity :
      Real.exp (-C * Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
        (S : ℝ) / (M : ℝ) / (((N + 1 : ℕ) : ℝ))) :
    (Z : ℝ) *
          Real.exp (-(C + Real.log 32) *
            Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
        (A : ℝ) ∧
      (B : ℝ) *
          Real.exp (-(C + Real.log 32) *
            Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
        4 * (X : ℝ) ^ 2 * (H : ℝ) := by
  constructor
  · exact q6_A_rate_absorption hC (by omega) hMZ hS hA hdensity
  · exact q6_H_rate_absorption hC hX hM hlarge hH
