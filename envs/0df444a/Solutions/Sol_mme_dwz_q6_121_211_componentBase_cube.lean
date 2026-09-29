-- Prove2me | solution 1 for mme_dwz_q6_121_211_componentBase_cube
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T06:17:32.03673+00:00
-- url     : https://prove2.me/submissions/6db6e8f8-c830-4669-b277-7a01b6d63e3b

import Mathlib.Tactic
import Definitions.Def_mme_dwz_square_data

open MME.DWZSquare

set_option autoImplicit false
set_option warningAsError true

theorem solution (tau : ℝ) :
    componentBase tau (13 : Fin 15) ^ (3 : ℕ) =
      4 * Real.rpow 6 (3 * tau) *
        (Real.rpow 6 (3 * tau) + 2) := by
  simp [componentBase]
  rw [mul_pow, mul_pow]
  have h2 :
      Real.rpow 2 ((2 : ℝ) / 3) ^ (3 : ℕ) = (4 : ℝ) := by
    change ((2 : ℝ) ^ ((2 : ℝ) / 3)) ^ (3 : ℕ) = 4
    calc
      ((2 : ℝ) ^ ((2 : ℝ) / 3)) ^ (3 : ℕ) =
          (2 : ℝ) ^ (((2 : ℝ) / 3) * (3 : ℝ)) :=
        (Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)
          ((2 : ℝ) / 3) 3).symm
      _ = 4 := by norm_num [Real.rpow_natCast]
  have h6 :
      Real.rpow 6 tau ^ (3 : ℕ) = Real.rpow 6 (3 * tau) := by
    change ((6 : ℝ) ^ tau) ^ (3 : ℕ) = (6 : ℝ) ^ (3 * tau)
    calc
      ((6 : ℝ) ^ tau) ^ (3 : ℕ) =
          (6 : ℝ) ^ (tau * (3 : ℝ)) :=
        (Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 6) tau 3).symm
      _ = (6 : ℝ) ^ (3 * tau) := by ring_nf
  have hsum :
      Real.rpow (Real.rpow 6 (3 * tau) + 2) ((1 : ℝ) / 3) ^ (3 : ℕ) =
        Real.rpow 6 (3 * tau) + 2 := by
    let Q : ℝ := Real.rpow 6 (3 * tau) + 2
    have hQ : 0 ≤ Q := by dsimp [Q]; positivity
    change (Q ^ ((1 : ℝ) / 3)) ^ (3 : ℕ) = Q
    convert Real.rpow_inv_natCast_pow hQ (by norm_num : (3 : ℕ) ≠ 0) using 1;
      norm_num [one_div]
  have h2' :
      ((2 : ℝ) ^ ((2 : ℝ) / 3)) ^ (3 : ℕ) = 4 := h2
  have h6' :
      ((6 : ℝ) ^ tau) ^ (3 : ℕ) = (6 : ℝ) ^ (3 * tau) := h6
  have hsum' :
      (((6 : ℝ) ^ (3 * tau) + 2) ^ ((3 : ℝ)⁻¹)) ^ (3 : ℕ) =
        (6 : ℝ) ^ (3 * tau) + 2 := by
    rw [show ((3 : ℝ)⁻¹) = (1 : ℝ) / 3 by norm_num]
    exact hsum
  rw [h2', h6', hsum']
