-- Prove2me | solution 1 for systemOfUnits.isMaximal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:42:57.289117+00:00
-- url     : https://prove2.me/submissions/5192162e-ea12-4dc6-a7be-2c4643beedce

module
public import Definitions.Def_FltRegular_NumberTheory_SystemOfUnits
public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
public import Mathlib.RingTheory.Henselian
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
public import Mathlib.LinearAlgebra.Dimension.Torsion.Basic
public import Definitions.Def_FltRegular_NumberTheory_Hilbert92
public import Theorems.Thm_systemOfUnits_finrank_spanA


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
include hp
namespace systemOfUnits
theorem _root_.solution [Module.Finite ℤ G] (hf : finrank ℤ G = s * (p - 1))
  [Module A G] (sys : systemOfUnits (G := G) p s) : sys.IsMaximal := by
  change (Submodule.span A (Set.range sys.units)).toAddSubgroup.FiniteIndex
  rw [AddSubgroup.finiteIndex_iff_finite_quotient]
  change Finite (G ⧸ Submodule.span A (Set.range sys.units))
  apply Module.finite_of_fg_torsion
  rw [← finrank_eq_zero_iff_isTorsion, Submodule.finrank_quotient,
    finrank_spanA p hp _ _ sys.linearIndependent, hf, mul_comm, Nat.sub_self]
end systemOfUnits
