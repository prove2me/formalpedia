-- Prove2me | solution 1 for flt5_cyc5_pid_descent_core
-- status  : ACCEPTED   (sketch)
-- author  : @tianyipeng
-- created : 2026-05-13T07:34:14.429692+00:00
-- url     : https://prove2.me/submissions/f8091bce-bc9d-4853-aa65-2b5586da2dbf

import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD
import Theorems.Thm_flt5_cyc5_pid_core_zz5_part
import Theorems.Thm_flt5_cyc5_pid_core_int_part

-- ============================================================
-- Sketch proof of flt5_cyc5_pid_descent_core (v3)
--
-- 2-child decomposition:
--   Child 1 (flt5_cyc5_pid_core_zz5_part):
--     ZZ5 PID argument:
--     Given gcd(a,b)=1 and Phi(a,b)=5*s^5, the PID on Z[ζ₅]
--     yields d ∈ Z[ζ₅] with N(d)^5 = s^5.
--     Proof: β₁ = (a+ζb)/λ is in Z[ζ₅], its norm is s^5.
--     By coprimeness (β₁⊥β₂β₃β₄) + PID → ∃ d, d^5 ~ β₁.
--     Then N(d)^5 = N(β₁) = s^5.
--
--   Child 2 (flt5_cyc5_pid_core_int_part):
--     Given d with N(d)^5 = s^5 and the descent hypotheses,
--     extract integer witnesses p, q with p^5+q^5=c1^5.
--     This is the Kummer witness extraction step.
-- ============================================================

theorem solution (a b c r s c1 : ℤ) (h_eq : a ^ 5 + b ^ 5 = c ^ 5)
    (h_cop : Int.gcd a b = 1) (h5c : (5 : ℤ) ∣ c) (hc : c ≠ 0) (hc1 : c = 5 * c1)
    (hw : a + b = 5 ^ 4 * r ^ 5)
    (hPhi : a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4 = 5 * s ^ 5)
    (hcop_rs : Int.gcd r s = 1) (hrs : r * s = c1)
    (hPID : IsPrincipalIdealRing (NumberField.RingOfIntegers (CyclotomicField 5 ℚ))) :
    ∃ p q : ℤ, p ^ 5 + q ^ 5 = c1 ^ 5 ∧ Int.gcd p q = 1 ∧ p ≠ 0 ∧ q ≠ 0 ∧ 0 < p * q := by
  -- Child 1: ZZ5 PID argument extracts d with norm^5 = s^5
  obtain ⟨d, hd_norm⟩ := flt5_cyc5_pid_core_zz5_part a b s h_cop hPhi hPID
  -- Child 2: Extract integer witnesses p, q from d
  exact flt5_cyc5_pid_core_int_part a b c r s c1
    h_eq h_cop h5c hc hc1 hw hPhi hcop_rs hrs d hd_norm hPID
