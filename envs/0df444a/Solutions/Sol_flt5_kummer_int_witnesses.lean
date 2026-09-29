-- Prove2me | solution 1 for flt5_kummer_int_witnesses
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @tianyipeng
-- created : 2026-05-13T08:55:37.018888+00:00
-- url     : https://prove2.me/submissions/17060db1-ed57-4de5-94b7-d646c0fb9ac6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD
import Theorems.Thm_flt5_kummer_descent_step

-- Sketch for flt5_kummer_int_witnesses
-- Strategy: Defer to flt5_kummer_descent_step which handles the full descent.
-- The descent: from d:ZZ5 with N(d)^5=s^5 and all FLT-5 hypotheses,
-- extract the ZZ5 coordinates of d as integers (p,q) satisfying p^5+q^5=c1^5.
-- This requires the specific structure of d coming from the Kummer factorization.

noncomputable section

abbrev ZZ5kw := NumberField.RingOfIntegers (CyclotomicField 5 ℚ)

instance : IsCyclotomicExtension {5} ℚ (CyclotomicField 5 ℚ) :=
  CyclotomicField.isCyclotomicExtension 5 ℚ

instance : NumberField (CyclotomicField 5 ℚ) :=
  IsCyclotomicExtension.numberField {5} ℚ (CyclotomicField 5 ℚ)

theorem solution (a b c r s c1 : ℤ)
    (h_eq : a ^ 5 + b ^ 5 = c ^ 5) (h_cop : Int.gcd a b = 1)
    (h5c : (5 : ℤ) ∣ c) (hc : c ≠ 0) (hc1 : c = 5 * c1)
    (hw : a + b = 5 ^ 4 * r ^ 5)
    (hPhi : a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4 = 5 * s ^ 5)
    (hcop_rs : Int.gcd r s = 1) (hrs : r * s = c1)
    (d : ZZ5kw) (hd_norm : (Algebra.norm ℤ d) ^ 5 = s ^ 5)
    (hPID : IsPrincipalIdealRing ZZ5kw) :
    ∃ p q : ℤ, p ^ 5 + q ^ 5 = c1 ^ 5 ∧ Int.gcd p q = 1 ∧
    p ≠ 0 ∧ q ≠ 0 ∧ 0 < p * q :=
  flt5_kummer_descent_step a b c r s c1 h_eq h_cop h5c hc hc1 hw hPhi hcop_rs hrs d hd_norm hPID

end
