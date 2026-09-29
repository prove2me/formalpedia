-- Prove2me | solution 1 for flt5_kummer_descent_step
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @tianyipeng
-- created : 2026-05-13T09:38:27.594686+00:00
-- url     : https://prove2.me/submissions/17c7902d-ae7c-4e3a-a1c2-bb9479b8cc26
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD
import Theorems.Thm_flt5_kummer_arith_descent

-- Sketch: flt5_kummer_descent_step
-- Goal: Given all FLT-5 hypotheses + d:ZZ5 with N(d)^5=s^5, find p,q with p^5+q^5=c1^5.
--
-- Key observation: N(d) is an integer satisfying N(d)^5 = s^5.
-- So we can pass N(d) to the pure arithmetic child flt5_kummer_arith_descent,
-- which extracts p,q using only integer arithmetic (no ZZ5 needed).
-- The ZZ5 element d serves as witness that the norm s is achievable; the actual
-- descent arithmetic goes through the integer norm N(d).

noncomputable section

instance : IsCyclotomicExtension {5} ℚ (CyclotomicField 5 ℚ) :=
  CyclotomicField.isCyclotomicExtension 5 ℚ

instance : NumberField (CyclotomicField 5 ℚ) :=
  IsCyclotomicExtension.numberField {5} ℚ (CyclotomicField 5 ℚ)

theorem solution (a b c r s c1 : ℤ) (h_eq : a ^ 5 + b ^ 5 = c ^ 5)
    (h_cop : Int.gcd a b = 1) (h5c : (5 : ℤ) ∣ c) (hc : c ≠ 0) (hc1 : c = 5 * c1)
    (hw : a + b = 5 ^ 4 * r ^ 5)
    (hPhi : a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4 = 5 * s ^ 5)
    (hcop_rs : Int.gcd r s = 1) (hrs : r * s = c1)
    (d : NumberField.RingOfIntegers (CyclotomicField 5 ℚ))
    (hd_norm : (Algebra.norm ℤ d) ^ 5 = s ^ 5)
    (hPID : IsPrincipalIdealRing (NumberField.RingOfIntegers (CyclotomicField 5 ℚ))) :
    ∃ p q : ℤ, p ^ 5 + q ^ 5 = c1 ^ 5 ∧ Int.gcd p q = 1 ∧ p ≠ 0 ∧ q ≠ 0 ∧ 0 < p * q := by
  -- Reduce to pure integer arithmetic: N(d):ℤ satisfies N(d)^5 = s^5
  -- Apply the arithmetic descent child: nd = Algebra.norm ℤ d is the 7th integer arg
  exact flt5_kummer_arith_descent a b c r s c1 (Algebra.norm ℤ d)
    h_eq h_cop h5c hc hc1 hw hPhi hcop_rs hrs hd_norm

end
