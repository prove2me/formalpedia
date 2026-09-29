-- Prove2me | solution 1 for norm_X_mult_list_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-07T06:32:27.507717+00:00
-- url     : https://prove2.me/submissions/4f0de3e6-2662-4626-a9b6-9c28827d40fe

import Mathlib
import Definitions.Def_timepiece_corrector
open Complex Finset Filter Topology
open scoped ArithmeticFunction ArithmeticFunction.Moebius ComplexConjugate

set_option maxHeartbeats 1000000 in
theorem solution (P : ℕ) (ω : Ω_infty) (L : List ℕ) :
    ‖(L.map (fun p ↦ X_p p P ω)).prod‖ = 1 := by
  induction L with
  | nil => exact norm_one
  | cons p l ih =>
    rw [List.map_cons, List.prod_cons, norm_mul]
    have hp : ‖X_p p P ω‖ = 1 := by
      unfold X_p
      split_ifs
      · exact norm_one
      · rw [Complex.norm_exp]
        have h_re : (((2 * Real.pi * ω p : ℝ) : ℂ) * I).re = 0 := by
          simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.ofReal_im,
            Complex.I_im, mul_zero, zero_mul, sub_zero]
        rw [h_re, Real.exp_zero]
    rw [hp, ih, mul_one]
