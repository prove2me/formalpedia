-- Prove2me | solution 1 for flt5_cyc5_pid_core_int_part
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @tianyipeng
-- created : 2026-05-13T08:13:26.373701+00:00
-- url     : https://prove2.me/submissions/996c575d-4d60-4e2e-98e2-760db5772d7d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD
import Theorems.Thm_flt5_kummer_int_witnesses

-- Sketch for flt5_cyc5_pid_core_int_part
-- Defers to flt5_kummer_int_witnesses: the full Kummer descent extraction.
-- Given d:ZZ5 with N(d)^5=s^5, r*s=c1, gcd(r,s)=1, and all FLT-5 hypotheses,
-- extract p,q with p^5+q^5=c1^5 via the Kummer argument.

theorem solution (a b c r s c1 : ℤ) (h_eq : a ^ 5 + b ^ 5 = c ^ 5)
    (h_cop : Int.gcd a b = 1) (h5c : (5 : ℤ) ∣ c) (hc : c ≠ 0) (hc1 : c = 5 * c1)
    (hw : a + b = 5 ^ 4 * r ^ 5)
    (hPhi : a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4 = 5 * s ^ 5)
    (hcop_rs : Int.gcd r s = 1) (hrs : r * s = c1)
    (d : NumberField.RingOfIntegers (CyclotomicField 5 ℚ))
    (hd_norm : (Algebra.norm ℤ d) ^ 5 = s ^ 5)
    (hPID : IsPrincipalIdealRing (NumberField.RingOfIntegers (CyclotomicField 5 ℚ))) :
    ∃ p q : ℤ, p ^ 5 + q ^ 5 = c1 ^ 5 ∧ Int.gcd p q = 1 ∧ p ≠ 0 ∧ q ≠ 0 ∧ 0 < p * q := by
  exact flt5_kummer_int_witnesses a b c r s c1 h_eq h_cop h5c hc hc1 hw hPhi hcop_rs hrs d hd_norm hPID
