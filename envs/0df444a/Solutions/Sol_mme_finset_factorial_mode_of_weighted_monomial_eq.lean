-- Prove2me | solution 1 for mme_finset_factorial_mode_of_weighted_monomial_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T20:30:47.901271+00:00
-- url     : https://prove2.me/submissions/ac5ba14a-7e6b-4c27-9a55-f8ba6475d57c

import Mathlib
import Theorems.Thm_mme_nat_pow_mul_factorial_le_self_pow_mul_factorial

open BigOperators

set_option autoImplicit false

/-- Equality of the weighted monomials lets the coordinatewise Poisson-mode
inequalities cancel, leaving a pure product-of-factorials comparison. -/
theorem solution {ι : Type} [Fintype ι] [DecidableEq ι]
    (w a : ι → ℕ) (hw : ∀ i, 0 < w i)
    (hpow : (∏ i, w i ^ a i) = ∏ i, w i ^ w i) :
    (∏ i, (w i).factorial) ≤ ∏ i, (a i).factorial := by
  have hcoordinate :
      (∏ i, (w i ^ a i) * (w i).factorial) ≤
        ∏ i, (w i ^ w i) * (a i).factorial := by
    exact Finset.prod_le_prod' fun i _ =>
      mme_nat_pow_mul_factorial_le_self_pow_mul_factorial (w i) (a i)
  have hcombined :
      (∏ i, w i ^ a i) * (∏ i, (w i).factorial) ≤
        (∏ i, w i ^ w i) * (∏ i, (a i).factorial) := by
    simpa only [Finset.prod_mul_distrib] using hcoordinate
  rw [hpow] at hcombined
  apply Nat.le_of_mul_le_mul_left hcombined
  exact Finset.prod_pos fun i _ => Nat.pow_pos (hw i)
