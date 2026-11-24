-- Prove2me | solution 1 for fltIdeals_coprime2_lemma
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:40:08.537282+00:00
-- url     : https://prove2.me/submissions/8f98f351-b7ec-410a-b9e9-e5c1011e4460

module
public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits
public import Definitions.Def_FltRegular_NumberTheory_Cyclotomic_CyclRat
public import Theorems.Thm_diff_of_roots

set_option autoImplicit false
@[expose] public section
public section
open FiniteDimensional Polynomial Algebra Nat Finset Fintype
variable (p : ℕ) (L : Type*) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
open scoped NumberField
open Ideal IsCyclotomicExtension
local notation "R" => 𝓞 (CyclotomicField p ℚ)
variable {p}
open IsPrimitiveRoot
theorem _root_.solution [Fact p.Prime] (ph : 5 ≤ p) {x y : ℤ} {η₁ η₂ : R}
    (hη₁ : η₁ ∈ nthRootsFinset p 1)
    (hη₂ : η₂ ∈ nthRootsFinset p 1) (hdiff : η₁ ≠ η₂) (hp : IsCoprime x y)
    (hp2 : ¬(p : ℤ) ∣ (x + y : ℤ)) (hwlog : η₁ ≠ 1) :
    (fltIdeals p x y hη₁) ⊔ (fltIdeals p x y hη₂) = ⊤ := by
  rw [fltIdeals, fltIdeals, Ideal.sup_eq_top_iff_isCoprime]
  have hdvd : (1 - η₁ : R) ∣ p := by
    rw [← neg_sub, neg_dvd]
    exact sub_one_dvd_natCast_of_pow_eq_one
      ((mem_nthRootsFinset (NeZero.pos p) 1).mp hη₁) hwlog
  have hcop : IsCoprime (1 - η₁ : R) (x + y : R) := by
    simpa only [map_add, eq_intCast] using
      (((Nat.prime_iff_prime_int.mp Fact.out).coprime_iff_not_dvd.mpr hp2).map
        (algebraMap ℤ R)).of_isCoprime_of_dvd_left hdvd
  have hroot : IsCoprime (x + η₁ * y : R) (1 - η₁) := by
    convert hcop.symm.add_mul_left_left (-y) using 1
    ring
  obtain ⟨u, hu⟩ := diff_of_roots ph hη₁ hη₂ hdiff hwlog
  have hdiff : IsCoprime (x + η₁ * y : R) ((η₁ - η₂) * y) := by
    rw [hu, mul_assoc, isCoprime_mul_unit_left_right u.isUnit]
    exact hroot.mul_right (hp.intCast.add_mul_right_left η₁)
  convert hdiff.neg_right.add_mul_right_right 1 using 1
  ring
