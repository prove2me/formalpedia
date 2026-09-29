-- Prove2me | solution 1 for selfbounding_resolution_quadratic_linear_bound
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-23T22:21:29.474056+00:00
-- url     : https://prove2.me/submissions/e49d7e65-7f48-4099-92ee-9bb8e19c36c8

import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
open Real

theorem solution :
    ∀ (EZ C A0 : ℝ), 0 ≤ EZ → 0 ≤ C → 0 ≤ A0 → A0 ≤ 1 →
      EZ ≤ C * A0 + C * A0 * Real.sqrt EZ →
      EZ ≤ 4 * (C + C ^ 2) * A0 := by
  intro EZ C A0 hEZ hC hA0 hA01 hrec
  set x := Real.sqrt EZ with hx
  have hx0 : 0 ≤ x := Real.sqrt_nonneg EZ
  have hx2 : x ^ 2 = EZ := by rw [hx, sq, Real.mul_self_sqrt hEZ]
  have hrec' : x ^ 2 ≤ C * A0 + C * A0 * x := by rw [hx2]; exact hrec
  rw [← hx2]
  nlinarith [sq_nonneg (x - 2 * C), mul_nonneg hC hA0, mul_nonneg (mul_nonneg hC hA0) hx0,
    mul_nonneg hC hx0, sq_nonneg x, mul_nonneg (mul_nonneg hC hC) hA0,
    mul_nonneg (sub_nonneg.mpr hA01) (mul_nonneg hC hx0),
    mul_nonneg (sub_nonneg.mpr hA01) (mul_nonneg (mul_nonneg hC hC) hx0),
    mul_nonneg hA0 (sq_nonneg (x - 2*C))]
