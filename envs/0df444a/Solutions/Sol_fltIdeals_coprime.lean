-- Prove2me | solution 1 for fltIdeals_coprime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:42:17.811269+00:00
-- url     : https://prove2.me/submissions/f4d484d1-a1d3-4931-8abc-32ffb925be52

module
public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits
public import Definitions.Def_FltRegular_NumberTheory_Cyclotomic_CyclRat
public import Theorems.Thm_aux_lem_flt
public import Theorems.Thm_fltIdeals_coprime2

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
theorem _root_.solution (hpri : p.Prime) (p5 : 5 ≤ p) {x y z : ℤ}
    (H : x ^ p + y ^ p = z ^ p) {η₁ η₂ : R} (hxy : IsCoprime x y)
    (hη₁ : η₁ ∈ nthRootsFinset p 1) (hη₂ : η₂ ∈ nthRootsFinset p 1)
    (hdiff : η₁ ≠ η₂)
    (caseI : ¬↑p ∣ x * y * z) :
    have : Fact p.Prime := ⟨hpri⟩
    IsCoprime (fltIdeals p x y hη₁) (fltIdeals p x y hη₂) := by
  have : Fact p.Prime := ⟨hpri⟩
  by_cases h : η₁ ≠ 1
  · exact fltIdeals_coprime2 p5 hη₁ hη₂ hdiff hxy (aux_lem_flt H caseI) h
  · have h2 : η₂ ≠ 1 := by
      simp only [ne_eq, not_not] at h
      rw [h] at hdiff
      exact hdiff.symm
    exact (fltIdeals_coprime2 p5 hη₂ hη₁ hdiff.symm hxy (aux_lem_flt H caseI) h2).symm
