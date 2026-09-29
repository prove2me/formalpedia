-- Prove2me | solution 1 for flt5_zz5_norm_lambda_cast
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-13T12:37:55.936024+00:00
-- url     : https://prove2.me/submissions/1f430de9-1431-4c51-b5cd-f717d5af73c9

import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Data.Int.Basic

-- Do NOT import Theorems.Thm_flt5_cyclotomic5_irred: imported theorems are Props,
-- not callable proof terms. Instead inline the proof.

noncomputable section

abbrev ZZ5c11 := NumberField.RingOfIntegers (CyclotomicField 5 ℚ)
abbrev CK5c11 := CyclotomicField 5 ℚ

instance inst1c11 : IsCyclotomicExtension {5} ℚ CK5c11 :=
  CyclotomicField.isCyclotomicExtension 5 ℚ

instance inst2c11 : NumberField CK5c11 :=
  IsCyclotomicExtension.numberField {5} ℚ CK5c11

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

theorem solution (ζ : ZZ5c11)
    (hζ : IsPrimitiveRoot (ζ : CK5c11) 5) :
    (Algebra.norm ℤ (1 - ζ : ZZ5c11) : ℚ) = 5 := by
  -- cyclotomic 5 ℚ is irreducible (inlined proof, not imported theorem)
  have hirr : Irreducible (Polynomial.cyclotomic 5 ℚ) :=
    Polynomial.cyclotomic.irreducible_rat (by decide)
  -- Norm over ℚ of (ζ - 1)
  have hQsub : Algebra.norm ℚ ((ζ : CK5c11) - 1) = 5 := by
    have h := IsPrimitiveRoot.norm_sub_one_of_prime_ne_two' hζ hirr (by norm_num)
    exact_mod_cast h
  -- Rank of CK5 over ℚ is 4
  have hfr : Module.finrank ℚ CK5c11 = 4 := by
    have h := IsCyclotomicExtension.finrank (K := ℚ) (L := CK5c11) (hirr := hirr)
    rw [show Nat.totient 5 = 4 from by decide] at h
    exact h
  -- Norm of -1 is 1
  have hNneg : Algebra.norm ℚ (-1 : CK5c11) = 1 := by
    rw [show (-1 : CK5c11) = algebraMap ℚ CK5c11 (-1) from by simp]
    rw [Algebra.norm_algebraMap, hfr]; norm_num
  -- Norm of (1 - ζ) over ℚ is 5
  have hQ : Algebra.norm ℚ (1 - (ζ : CK5c11)) = 5 := by
    rw [show (1 : CK5c11) - ζ = (-1) * (ζ - 1) from by ring]
    rw [(Algebra.norm ℚ).map_mul, hNneg, one_mul, hQsub]
  -- Algebra.coe_norm_int: (Algebra.norm ℤ x : ℚ) = Algebra.norm ℚ (x : K)
  -- ZZ5c11 is a subtype of CK5c11; the coercion preserves ring ops definitionally
  rw [Algebra.coe_norm_int]
  -- Goal: Algebra.norm ℚ ((1 - ζ : ZZ5c11) : CK5c11) = 5
  -- ((1 - ζ : ZZ5c11) : CK5c11) = 1 - (ζ : CK5c11) definitionally (subtype.val)
  have hcoerce : ((1 - ζ : ZZ5c11) : CK5c11) = 1 - (ζ : CK5c11) := rfl
  rw [hcoerce]
  exact hQ

end
