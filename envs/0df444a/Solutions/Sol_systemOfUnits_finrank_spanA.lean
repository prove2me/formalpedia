-- Prove2me | solution 1 for systemOfUnits.finrank_spanA
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:42:15.870885+00:00
-- url     : https://prove2.me/submissions/1d96a6df-d4e9-4df9-bb1d-a5dbb0699998

module
public import Definitions.Def_FltRegular_NumberTheory_CyclotomicRing
public import Definitions.Def_FltRegular_NumberTheory_SystemOfUnits
public import Theorems.Thm_CyclotomicIntegers_powerBasis_dim


set_option autoImplicit false
@[expose] public section
public section
open FiniteDimensional
open NumberField
variable (p : ℕ) (hp : Nat.Prime p)
open Module Finset
variable (G : Type*) [AddCommGroup G] (s : ℕ) (hf : finrank ℤ G = s * (p - 1))
local notation "A" => (CyclotomicIntegers p)
variable [Module (CyclotomicIntegers p) G]
open systemOfUnits
include hp
namespace systemOfUnits
theorem _root_.solution {R : ℕ} (f : Fin R → G) (hf : LinearIndependent A f) :
    finrank ℤ (Submodule.span A (Set.range f)) = (p - 1) * R := by
  have := Fact.mk hp
  have := Module.Free.of_basis (Basis.span hf)
  have := Module.Finite.of_basis (Basis.span hf)
  rw [← finrank_mul_finrank ℤ A, finrank_span_eq_card hf, Fintype.card_fin,
    PowerBasis.finrank (CyclotomicIntegers.powerBasis p), CyclotomicIntegers.powerBasis_dim]
end systemOfUnits
