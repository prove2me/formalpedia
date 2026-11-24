-- Prove2me | solution 1 for diff_of_roots
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:39:23.037019+00:00
-- url     : https://prove2.me/submissions/091ac37f-5733-45c1-b5fc-acac96946e2a

module
public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits
public import Definitions.Def_FltRegular_NumberTheory_Cyclotomic_CyclRat

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
theorem _root_.solution [hp : Fact p.Prime] (ph : 5 ≤ p) {η₁ η₂ : R}
    (hη₁ : η₁ ∈ nthRootsFinset p 1) (hη₂ : η₂ ∈ nthRootsFinset p 1)
    (hdiff : η₁ ≠ η₂) (hwlog : η₁ ≠ 1) :
    ∃ u : Rˣ, η₁ - η₂ = u * (1 - η₁) := by
  have _ : 2 ≤ p := le_trans (by decide) ph
  have h := isPrimitiveRoot_of_mem_nthRootsFinset Fact.out hη₁ hwlog
  rcases h.nthRootsFinset_pairwise_associated_sub_one_sub_of_prime hp.out hη₁ hη₂ hdiff with
    ⟨u, hu⟩
  exact ⟨-u, by grind [Units.val_neg]⟩
