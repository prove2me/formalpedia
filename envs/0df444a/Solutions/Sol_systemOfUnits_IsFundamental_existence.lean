-- Prove2me | solution 1 for systemOfUnits.IsFundamental.existence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:47:01.011201+00:00
-- url     : https://prove2.me/submissions/ba9cd87f-a894-41b7-b8d5-0ade2d74be04

module
public import Definitions.Def_FltRegular_NumberTheory_SystemOfUnits
public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
public import Mathlib.RingTheory.Henselian
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
public import Mathlib.LinearAlgebra.Dimension.Torsion.Basic
public import Definitions.Def_FltRegular_NumberTheory_Hilbert92
public import Theorems.Thm_systemOfUnits_isMaximal
public import Theorems.Thm_systemOfUnits_existence


set_option autoImplicit false
@[expose] public section
public section
open scoped NumberField nonZeroDivisors
open FiniteDimensional NumberField
variable {s r : ℕ} (p : ℕ) {K : Type*} [Field K]
variable {k : Type*} [Field k] (hp : Nat.Prime p)
open Module Finset
open CyclotomicIntegers (zeta)
variable (G : Type*) [AddCommGroup G]
local notation3 "A" => CyclotomicIntegers p
open systemOfUnits systemOfUnits.IsFundamental
variable {H : Type*} [CommGroup H] [Fintype H] (hCard : Fintype.card H = p)
  (σ : H) (hσ : Subgroup.zpowers σ = ⊤) (s : ℕ) [DistribMulAction H G]
  (hf : finrank ℤ G = s * (p - 1))
include hp hf
variable [Module.Finite ℤ G]
namespace systemOfUnits.IsFundamental
theorem _root_.solution [Module.Free ℤ G] [Module A G] :
    ∃ S : systemOfUnits p G s, S.IsFundamental := by
  obtain ⟨S⟩ := systemOfUnits.existence p hp G s hf
  let := S.isMaximal p hp G hf
  have : { a | ∃ (S : systemOfUnits p G s) (_ : S.IsMaximal), a = S.index p G }.Nonempty :=
    ⟨S.index, S, S.isMaximal p hp G hf, rfl⟩
  obtain ⟨S', hS', ha⟩ := Nat.sInf_mem this
  use S', hS'
  intro a' ha'
  rw [← ha]
  apply csInf_le (OrderBot.bddBelow _)
  use a', ha'
end systemOfUnits.IsFundamental
