-- Prove2me | solution 1 for levy_foundations_arrivalSurvivalPolynomialDerivative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T00:32:24.651365+00:00
-- url     : https://prove2.me/submissions/9fd76f1e-a715-4da8-a37d-d3bbfe1be9c2

import Mathlib.Probability.Distributions.Gamma
import Definitions.Def_levy_foundations_arrivalSurvivalPolynomial
import Definitions.Def_levy_foundations_arrivalGammaDensityReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory

theorem solution (R : ℝ) (n : ℕ) (s : ℝ) :
    HasDerivAt (LevyFoundations.arrivalSurvivalPolynomial R n)
      (-LevyFoundations.arrivalGammaDensityReal R n s) s := by
  induction n with
  | zero =>
    have hfun : LevyFoundations.arrivalSurvivalPolynomial R 0 =
        fun s => Real.exp (-(R * s)) := by
      funext s
      simp [LevyFoundations.arrivalSurvivalPolynomial]
    rw [hfun]
    have h1 : HasDerivAt (fun s => Real.exp (-(R * s)))
        (Real.exp (-(R * s)) * -(R * 1)) s :=
      (((hasDerivAt_id s).const_mul R).neg).exp
    convert h1 using 1
    rw [LevyFoundations.arrivalGammaDensityReal]
    ring
  | succ n ih =>
    have hsplit : LevyFoundations.arrivalSurvivalPolynomial R (n + 1) =
        fun s => LevyFoundations.arrivalSurvivalPolynomial R n s +
          Real.exp (-(R * s)) *
            ((R * s) ^ (n + 1) / ((n + 1).factorial : ℝ)) := by
      funext s
      simp only [LevyFoundations.arrivalSurvivalPolynomial,
        Finset.sum_range_succ, mul_add]
    rw [hsplit]
    have hE : HasDerivAt (fun s => Real.exp (-(R * s)))
        (Real.exp (-(R * s)) * -(R * 1)) s :=
      (((hasDerivAt_id s).const_mul R).neg).exp
    have hP : HasDerivAt (fun s => (R * s) ^ (n + 1))
        ((n + 1 : ℕ) * (R * s) ^ (n + 1 - 1) * (R * 1)) s :=
      ((hasDerivAt_id s).const_mul R).pow (n + 1)
    have hg := hE.mul (hP.div_const ((n + 1).factorial : ℝ))
    refine (ih.add hg).congr_deriv ?_
    simp only [LevyFoundations.arrivalGammaDensityReal, Nat.factorial_succ]
    push_cast
    field_simp
    ring
