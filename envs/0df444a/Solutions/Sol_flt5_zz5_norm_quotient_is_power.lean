-- Prove2me | solution 1 for flt5_zz5_norm_quotient_is_power
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @tianyipeng
-- created : 2026-05-13T09:33:25.917672+00:00
-- url     : https://prove2.me/submissions/f516647f-ee35-4f23-bb1c-d75bde681288
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.Linarith
import Theorems.Thm_flt5_zz5_norm_lambda_eq_five
import Theorems.Thm_flt5_zz5_norm_numerator_eq_phi

-- Sketch: flt5_zz5_norm_quotient_is_power
-- Goal: Algebra.norm ℤ γ = s^5 given (a+ζb) = (1-ζ)*γ and Phi(a,b) = 5*s^5
--
-- Key chain:
--   5 * N(γ) = N(1-ζ) * N(γ)        [by hN_lam: N(1-ζ)=5]
--            = N((1-ζ)*γ)            [map_mul for Algebra.norm ℤ]
--            = N(a+ζb)               [by ← hγ]
--            = Phi(a,b)              [by hN_num]
--            = 5 * s^5               [by hPhi]
--   Hence N(γ) = s^5 by linarith.

noncomputable section

abbrev ZZ5nq := NumberField.RingOfIntegers (CyclotomicField 5 ℚ)

instance : IsCyclotomicExtension {5} ℚ (CyclotomicField 5 ℚ) :=
  CyclotomicField.isCyclotomicExtension 5 ℚ

instance : NumberField (CyclotomicField 5 ℚ) :=
  IsCyclotomicExtension.numberField {5} ℚ (CyclotomicField 5 ℚ)

theorem solution (a b s : ℤ) (h_cop : Int.gcd a b = 1)
    (hPhi : a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4 = 5 * s ^ 5)
    (ζ : ZZ5nq) (hζ : IsPrimitiveRoot (ζ : CyclotomicField 5 ℚ) 5)
    (γ : ZZ5nq)
    (hγ : (a : ZZ5nq) + ζ * (b : ZZ5nq) = (1 - ζ) * γ)
    (hPID : IsPrincipalIdealRing ZZ5nq) :
    Algebra.norm ℤ γ = s ^ 5 := by
  have hN_lam : Algebra.norm ℤ (1 - ζ : ZZ5nq) = 5 :=
    flt5_zz5_norm_lambda_eq_five ζ hζ
  have hN_num : Algebra.norm ℤ ((a : ZZ5nq) + ζ * b) =
      a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4 :=
    flt5_zz5_norm_numerator_eq_phi a b ζ hζ
  have h : 5 * Algebra.norm ℤ γ = 5 * s ^ 5 := calc
      5 * Algebra.norm ℤ γ
          = Algebra.norm ℤ (1 - ζ) * Algebra.norm ℤ γ := by rw [← hN_lam]
        _ = Algebra.norm ℤ ((1 - ζ) * γ) := (map_mul (Algebra.norm ℤ) _ _).symm
        _ = Algebra.norm ℤ ((a : ZZ5nq) + ζ * b) := by rw [← hγ]
        _ = a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4 := hN_num
        _ = 5 * s ^ 5 := hPhi
  linarith

end
