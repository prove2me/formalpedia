-- Prove2me | solution 1 for fltIdeals_coprime2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:41:05.24512+00:00
-- url     : https://prove2.me/submissions/7e19c047-3a47-421b-83c4-99e8c554d1e3

module
public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits
public import Definitions.Def_FltRegular_NumberTheory_Cyclotomic_CyclRat
public import Theorems.Thm_fltIdeals_coprime2_lemma

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
    (hη₁ : η₁ ∈ nthRootsFinset p 1) (hη₂ : η₂ ∈ nthRootsFinset p 1)
    (hdiff : η₁ ≠ η₂) (hp : IsCoprime x y)
    (hp2 : ¬(p : ℤ) ∣ (x + y : ℤ)) (hwlog : η₁ ≠ 1) :
    IsCoprime (fltIdeals p x y hη₁) (fltIdeals p x y hη₂) := by
  simpa [Ideal.isCoprime_iff_add] using
    fltIdeals_coprime2_lemma ph hη₁ hη₂ hdiff hp hp2 hwlog
