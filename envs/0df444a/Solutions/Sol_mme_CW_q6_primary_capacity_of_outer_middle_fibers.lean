-- Prove2me | solution 1 for mme_CW_q6_primary_capacity_of_outer_middle_fibers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T17:43:58.704816+00:00
-- url     : https://prove2.me/submissions/7e83193e-6ebf-4b9d-9410-9a05c234ae55

import Mathlib.Analysis.SpecialFunctions.Exp

open Real

theorem solution
    (N Z X B A H : ℕ) (loss : ℝ)
    (hX : 0 < X)
    (houter :
      (Z : ℝ) * Real.exp (-((N : ℝ) * loss / 12)) ≤ (A : ℝ))
    (hmiddle :
      (B : ℝ) * Real.exp (-((N : ℝ) * loss / 8)) ≤
        4 * (X : ℝ) ^ 2 * (H : ℝ)) :
    (((Z : ℝ) ^ 3 * (B : ℝ) ^ 2) /
        (16 * (X : ℝ) ^ 4)) *
          Real.exp (-((N : ℝ) * loss / 2)) ≤
      ((A ^ 3 : ℕ) : ℝ) * (H : ℝ) ^ 2 := by
  have hXr : (0 : ℝ) < X := by exact_mod_cast hX
  have hZnonneg : (0 : ℝ) ≤ Z := by positivity
  have hBnonneg : (0 : ℝ) ≤ B := by positivity
  have houterLeftNonneg :
      0 ≤ (Z : ℝ) * Real.exp (-((N : ℝ) * loss / 12)) :=
    mul_nonneg hZnonneg (Real.exp_pos _).le
  have hmiddleLeftNonneg :
      0 ≤ (B : ℝ) * Real.exp (-((N : ℝ) * loss / 8)) :=
    mul_nonneg hBnonneg (Real.exp_pos _).le
  have houterCube := pow_le_pow_left₀ houterLeftNonneg houter 3
  have hmiddleSquare :=
    mul_self_le_mul_self hmiddleLeftNonneg hmiddle
  have hXfour : (0 : ℝ) < 16 * (X : ℝ) ^ 4 := by positivity
  calc
    (((Z : ℝ) ^ 3 * (B : ℝ) ^ 2) /
          (16 * (X : ℝ) ^ 4)) *
        Real.exp (-((N : ℝ) * loss / 2)) =
        (((Z : ℝ) * Real.exp (-((N : ℝ) * loss / 12))) ^ 3 /
          (16 * (X : ℝ) ^ 4)) *
          (((B : ℝ) * Real.exp (-((N : ℝ) * loss / 8))) *
            ((B : ℝ) * Real.exp (-((N : ℝ) * loss / 8)))) := by
              rw [show -((N : ℝ) * loss / 2) =
                  -((N : ℝ) * loss / 12) +
                    (-((N : ℝ) * loss / 12) +
                      (-((N : ℝ) * loss / 12) +
                        (-((N : ℝ) * loss / 8) +
                          -((N : ℝ) * loss / 8)))) by ring,
                Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_add]
              ring
    _ ≤ ((A : ℝ) ^ 3 / (16 * (X : ℝ) ^ 4)) *
          ((4 * (X : ℝ) ^ 2 * (H : ℝ)) *
            (4 * (X : ℝ) ^ 2 * (H : ℝ))) := by
      have houterCubeDiv :
          ((Z : ℝ) * Real.exp (-((N : ℝ) * loss / 12))) ^ 3 /
              (16 * (X : ℝ) ^ 4) ≤
            (A : ℝ) ^ 3 / (16 * (X : ℝ) ^ 4) :=
        (div_le_div_iff_of_pos_right hXfour).2 houterCube
      exact mul_le_mul houterCubeDiv hmiddleSquare
        (by positivity) (by positivity)
    _ = (A : ℝ) ^ 3 * (H : ℝ) ^ 2 := by
      field_simp
      ring
    _ = ((A ^ 3 : ℕ) : ℝ) * (H : ℝ) ^ 2 := by norm_num
