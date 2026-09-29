-- Prove2me | solution 1 for mme_dwz_table2_exact_hash_lower_eventually_two_groups
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T20:06:00.220403+00:00
-- url     : https://prove2.me/submissions/c8fd8550-084f-43fd-85d2-faa1e3638633

import Definitions.Def_mme_dwz_square_data
import Theorems.Thm_mme_dwz_square_retained_log_rate_gt_157133
import Theorems.Thm_mme_floor_behrend_polynomial_loss_ge_exp_sqrt
import Theorems.Thm_mme_dwz_table2_retained_polynomial_denominator_le_exp_sqrt
import Theorems.Thm_mme_eventually_linear_le_exp_linear_sub_sqrt

open Filter Topology
open MME.DWZSquare

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 100000

theorem solution :
    ∀ᶠ L : ℕ in atTop,
      ∀ p : ℕ, 2 ≤ p →
        (p : ℝ) ≤ Real.exp (16 * (((L + 1 : ℕ) : ℝ))) →
        let x : ℝ := (((L + 1 : ℕ) : ℝ))
        let jointPoly : ℝ := (6 * x) ^ 15
        let degreePoly : ℝ := (6 * x) ^ 5 * x ^ 15
        let zPoly : ℝ := (6 * x) ^ 5
        let compatibilityPoly : ℝ := (6 * x) ^ 9
        let Dhash : ℝ :=
          32 * max (jointPoly * degreePoly) (zPoly * compatibilityPoly)
        2 * ((8 * (4 * L + 1) : ℕ) : ℝ) ≤
          Real.rpow 2 (retainedLogRate * (L : ℝ)) *
            (((((p / 2 : ℕ) : ℝ) / (p : ℝ)) *
                Real.exp
                  (-4 * Real.sqrt
                    (Real.log (((p / 2 : ℕ) : ℝ))))) /
              Dhash) := by
  let B : ℝ := 32 * 6 ^ 20 * ((70 : ℕ).factorial : ℝ)
  let C : ℝ := 4 + 4 * ((16 : ℝ) + 1) + B
  let b : ℝ := (157133 / 100000 : ℝ) * Real.log 2
  have hb : 0 < b := by
    dsimp only [b]
    positivity
  have hC : 0 ≤ C := by
    dsimp only [C, B]
    positivity
  have hdom :=
    mme_eventually_linear_le_exp_linear_sub_sqrt 64 b C
      (by norm_num) hb hC
  filter_upwards [hdom] with L hdomL
  intro p hp hpUpper
  dsimp only
  let x : ℝ := (((L + 1 : ℕ) : ℝ))
  let jointPoly : ℝ := (6 * x) ^ 15
  let degreePoly : ℝ := (6 * x) ^ 5 * x ^ 15
  let zPoly : ℝ := (6 * x) ^ 5
  let compatibilityPoly : ℝ := (6 * x) ^ 9
  let Dhash : ℝ :=
    32 * max (jointPoly * degreePoly) (zPoly * compatibilityPoly)
  have hDpos : 0 < Dhash := by
    dsimp only [Dhash, jointPoly, degreePoly, zPoly,
      compatibilityPoly, x]
    positivity
  have hDUpper :
      Dhash ≤ Real.exp (B * Real.sqrt (((L + 1 : ℕ) : ℝ))) := by
    simpa only [Dhash, jointPoly, degreePoly, zPoly,
      compatibilityPoly, x, B] using
      mme_dwz_table2_retained_polynomial_denominator_le_exp_sqrt L
  have hloss :=
    mme_floor_behrend_polynomial_loss_ge_exp_sqrt
      L p Dhash 16 B (by norm_num) hp hpUpper hDpos hDUpper
  have hrate :
      Real.exp (b * (L : ℝ)) ≤
        Real.rpow 2 (retainedLogRate * (L : ℝ)) := by
    change Real.exp (b * (L : ℝ)) ≤
      (2 : ℝ) ^ (retainedLogRate * (L : ℝ))
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    apply Real.exp_le_exp.mpr
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hL : (0 : ℝ) ≤ (L : ℝ) := by positivity
    have hr := mme_dwz_square_retained_log_rate_gt_157133
    calc
      b * (L : ℝ) =
          (157133 / 100000 : ℝ) * (Real.log 2 * (L : ℝ)) := by
            dsimp only [b]
            ring
      _ ≤ retainedLogRate * (Real.log 2 * (L : ℝ)) :=
        mul_le_mul_of_nonneg_right (le_of_lt hr)
          (mul_nonneg (le_of_lt hlog) hL)
      _ = Real.log 2 * (retainedLogRate * (L : ℝ)) := by ring
  have hproduct :
      Real.exp
          (b * (L : ℝ) - C * Real.sqrt (((L + 1 : ℕ) : ℝ))) ≤
        Real.rpow 2 (retainedLogRate * (L : ℝ)) *
          (((((p / 2 : ℕ) : ℝ) / (p : ℝ)) *
              Real.exp
                (-4 * Real.sqrt
                  (Real.log (((p / 2 : ℕ) : ℝ))))) /
            Dhash) := by
    have hloss' :
        Real.exp (-C * Real.sqrt (((L + 1 : ℕ) : ℝ))) ≤
          (((p / 2 : ℕ) : ℝ) / (p : ℝ)) *
              Real.exp
                (-4 * Real.sqrt
                  (Real.log (((p / 2 : ℕ) : ℝ)))) /
            Dhash := by
      change
        Real.exp
            (-(4 + 4 * ((16 : ℝ) + 1) + B) *
              Real.sqrt (((L + 1 : ℕ) : ℝ))) ≤
          (((p / 2 : ℕ) : ℝ) / (p : ℝ)) *
              Real.exp
                (-4 * Real.sqrt
                  (Real.log (((p / 2 : ℕ) : ℝ)))) /
            Dhash
      exact hloss
    rw [show b * (L : ℝ) - C * Real.sqrt (((L + 1 : ℕ) : ℝ)) =
        b * (L : ℝ) + (-C * Real.sqrt (((L + 1 : ℕ) : ℝ))) by ring,
      Real.exp_add]
    exact mul_le_mul hrate hloss' (Real.exp_nonneg _)
      (Real.rpow_nonneg (by norm_num) _)
  calc
    2 * ((8 * (4 * L + 1) : ℕ) : ℝ)
        ≤ 64 * (((L + 1 : ℕ) : ℝ)) := by
      push_cast
      nlinarith [show (0 : ℝ) ≤ (L : ℝ) by positivity]
    _ ≤ Real.exp
          (b * (L : ℝ) - C * Real.sqrt (((L + 1 : ℕ) : ℝ))) := hdomL
    _ ≤ _ := by
      simpa only [Dhash, jointPoly, degreePoly, zPoly,
        compatibilityPoly, x] using hproduct
