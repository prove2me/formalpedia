-- Prove2me | solution 1 for matrix_khintchine_log_window_dimension_factor
-- status  : ACCEPTED   (prove)
-- author  : @Minghui
-- created : 2026-06-25T21:00:26.402132+00:00
-- url     : https://prove2.me/submissions/806ea92f-0673-4739-9a63-6eade60e4ec2

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Real.Archimedean

open scoped Classical BigOperators

theorem solution :
    ∃ Cwin : ℝ, 0 < Cwin ∧
      ∀ {d N : ℕ}, 0 < d → 2 ≤ N → d ≤ N * N →
        ∃ p : ℕ, 1 ≤ p ∧
          Real.sqrt (2 * (p : ℝ)) *
              (d : ℝ) ^ ((1 : ℝ) / (2 * (p : ℝ))) ≤
            Cwin * Real.sqrt (Real.log (N : ℝ)) := by
  let B : ℝ := 2 + (Real.log 2)⁻¹
  let A : ℝ := 2 * B
  refine ⟨3 * Real.sqrt A, ?_, ?_⟩
  · have hlog2_pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    have hB_pos : 0 < B := by
      dsimp [B]
      have hinv_pos : 0 < (Real.log (2 : ℝ))⁻¹ := inv_pos.mpr hlog2_pos
      linarith
    have hA_pos : 0 < A := by
      dsimp [A]
      exact mul_pos (by norm_num) hB_pos
    exact mul_pos (by norm_num) (Real.sqrt_pos.2 hA_pos)
  · intro d N hd hN hdle
    let M : ℕ := N * N
    let p : ℕ := Nat.ceil (Real.log (M : ℝ))
    have hN_real_gt_one : (1 : ℝ) < (N : ℝ) := by
      have hN_nat : 1 < N := lt_of_lt_of_le (by decide : 1 < 2) hN
      exact_mod_cast hN_nat
    have hN_real_pos : 0 < (N : ℝ) := lt_trans zero_lt_one hN_real_gt_one
    have hM_cast : (M : ℝ) = (N : ℝ) * (N : ℝ) := by
      dsimp [M]
      norm_num
    have hM_real_gt_one : (1 : ℝ) < (M : ℝ) := by
      rw [hM_cast]
      nlinarith [hN_real_gt_one]
    have hM_pos : 0 < (M : ℝ) := lt_trans zero_lt_one hM_real_gt_one
    have hlogM_pos : 0 < Real.log (M : ℝ) := Real.log_pos hM_real_gt_one
    have hp_pos : 0 < p := by
      dsimp [p]
      exact Nat.ceil_pos.mpr hlogM_pos
    have hp_one : 1 ≤ p := Nat.succ_le_of_lt hp_pos
    refine ⟨p, hp_one, ?_⟩
    have hp_real_pos : 0 < (p : ℝ) := by exact_mod_cast hp_pos
    have htwo_p_pos : 0 < 2 * (p : ℝ) := by positivity
    have hlogM_le_p : Real.log (M : ℝ) ≤ (p : ℝ) := by
      dsimp [p]
      exact Nat.le_ceil _
    have hpow_d_le_exp :
        (d : ℝ) ^ ((1 : ℝ) / (2 * (p : ℝ))) ≤ Real.exp 1 := by
      have hd_nonneg : 0 ≤ (d : ℝ) := by positivity
      have hdle_real : (d : ℝ) ≤ (M : ℝ) := by
        dsimp [M]
        exact_mod_cast hdle
      have hexp_nonneg : 0 ≤ (1 : ℝ) / (2 * (p : ℝ)) := by positivity
      have hd_to_M := Real.rpow_le_rpow hd_nonneg hdle_real hexp_nonneg
      refine hd_to_M.trans ?_
      rw [Real.rpow_def_of_pos hM_pos]
      apply Real.exp_le_exp.mpr
      have hlogM_le_two_p : Real.log (M : ℝ) ≤ 2 * (p : ℝ) := by nlinarith
      have hfrac : Real.log (M : ℝ) / (2 * (p : ℝ)) ≤ 1 := by
        exact (div_le_one htwo_p_pos).mpr hlogM_le_two_p
      have hmul_eq : Real.log (M : ℝ) * (1 / (2 * (p : ℝ))) =
          Real.log (M : ℝ) / (2 * (p : ℝ)) := by ring
      rwa [hmul_eq]
    have hpow_d_le_three :
        (d : ℝ) ^ ((1 : ℝ) / (2 * (p : ℝ))) ≤ 3 :=
      hpow_d_le_exp.trans (le_of_lt Real.exp_one_lt_three)
    have hlogM_eq : Real.log (M : ℝ) = 2 * Real.log (N : ℝ) := by
      rw [hM_cast, Real.log_mul hN_real_pos.ne' hN_real_pos.ne']
      ring
    have hlog2_pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    have hlog2_le_L : Real.log (2 : ℝ) ≤ Real.log (N : ℝ) := by
      exact Real.log_le_log (by norm_num) (by exact_mod_cast hN)
    have hone_le_inv_mul_L : (1 : ℝ) ≤ (Real.log (2 : ℝ))⁻¹ * Real.log (N : ℝ) := by
      have hone_le_div : (1 : ℝ) ≤ Real.log (N : ℝ) / Real.log (2 : ℝ) := by
        rw [le_div_iff₀ hlog2_pos]
        simpa using hlog2_le_L
      rwa [div_eq_mul_inv, mul_comm] at hone_le_div
    have hp_le_BL : (p : ℝ) ≤ B * Real.log (N : ℝ) := by
      have hp_le_logM_add_one : (p : ℝ) ≤ Real.log (M : ℝ) + 1 := by
        exact le_of_lt (by dsimp [p]; exact Nat.ceil_lt_add_one (le_of_lt hlogM_pos))
      dsimp [B]
      rw [hlogM_eq] at hp_le_logM_add_one
      nlinarith
    have hA_nonneg : 0 ≤ A := by
      have hB_pos : 0 < B := by
        dsimp [B]
        have hinv_pos : 0 < (Real.log (2 : ℝ))⁻¹ := inv_pos.mpr hlog2_pos
        linarith
      dsimp [A]
      exact le_of_lt (mul_pos (by norm_num) hB_pos)
    have hsqrt_factor :
        Real.sqrt (2 * (p : ℝ)) ≤ Real.sqrt A * Real.sqrt (Real.log (N : ℝ)) := by
      have harg : 2 * (p : ℝ) ≤ A * Real.log (N : ℝ) := by
        dsimp [A]
        nlinarith
      calc
        Real.sqrt (2 * (p : ℝ)) ≤ Real.sqrt (A * Real.log (N : ℝ)) :=
          Real.sqrt_le_sqrt harg
        _ = Real.sqrt A * Real.sqrt (Real.log (N : ℝ)) := by
          rw [Real.sqrt_mul hA_nonneg]
    have hpow_nonneg : 0 ≤ (d : ℝ) ^ ((1 : ℝ) / (2 * (p : ℝ))) := by
      exact Real.rpow_nonneg (by positivity) _
    have hupper_nonneg : 0 ≤ Real.sqrt A * Real.sqrt (Real.log (N : ℝ)) := by positivity
    have hmul := mul_le_mul hsqrt_factor hpow_d_le_three hpow_nonneg hupper_nonneg
    calc
      Real.sqrt (2 * (p : ℝ)) * (d : ℝ) ^ ((1 : ℝ) / (2 * (p : ℝ)))
          ≤ (Real.sqrt A * Real.sqrt (Real.log (N : ℝ))) * 3 := hmul
      _ = (3 * Real.sqrt A) * Real.sqrt (Real.log (N : ℝ)) := by ring
