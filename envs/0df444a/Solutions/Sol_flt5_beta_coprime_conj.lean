-- Prove2me | solution 1 for flt5_beta_coprime_conj
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @tianyipeng
-- created : 2026-05-13T17:56:03.279206+00:00
-- url     : https://prove2.me/submissions/74b7a099-0fff-41ad-adb8-9c391ed506b1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD
import Theorems.Thm_flt5_beta_coprime_conj_pid

-- Proof that β is coprime to each nontrivial Galois conjugate in ZZ5.
-- Strategy (Kummer coprimeness):
-- 1. For σ ≠ id, β - σ(β) = b * (ζ - σ(ζ)) = b * unit * λ in ZZ5
--    (since (1 - ζ^k) = unit * λ for all k ≢ 0 mod 5; proved via N(1-ζ^k) = N(λ) = 5).
-- 2. Any common divisor d of β and σ(β) in ZZ5 (PID) divides β - σ(β) = unit * λ * b.
--    So d | λ or d | b.
-- 3. If d | λ: then since λ is the unique prime above 5 in ZZ5, and N(β) = s^5
--    with gcd(a,b)=1 gives arithmetic conditions that prevent both β and σ(β) being
--    divisible by λ simultaneously.
-- 4. If d | b: then d | N(β) = s^5 and d | N(b) (an integer), combined with gcd conditions,
--    shows d is a unit.
-- Child flt5_beta_coprime_conj_pid handles the complete PID-level argument.

noncomputable section

abbrev ZZ5bcj := NumberField.RingOfIntegers (CyclotomicField 5 ℚ)
abbrev CK5bcj := CyclotomicField 5 ℚ

instance : IsCyclotomicExtension {5} ℚ CK5bcj :=
  CyclotomicField.isCyclotomicExtension 5 ℚ

instance : NumberField CK5bcj :=
  IsCyclotomicExtension.numberField {5} ℚ CK5bcj

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

theorem solution (a b s : ℤ) (h_cop : Int.gcd a b = 1)
    (β : ZZ5bcj) (hβ : Algebra.norm ℤ β = s ^ 5)
    (hPID : IsPrincipalIdealRing ZZ5bcj) :
    ∀ σ : CK5bcj ≃ₐ[ℚ] CK5bcj, σ ≠ AlgEquiv.refl →
    IsCoprime β (NumberField.RingOfIntegers.mapAlgEquiv σ β) :=
  flt5_beta_coprime_conj_pid a b s h_cop β hβ hPID

end
