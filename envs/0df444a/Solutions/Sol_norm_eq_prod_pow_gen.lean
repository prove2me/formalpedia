-- Prove2me | solution 1 for norm_eq_prod_pow_gen
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:42:13.96929+00:00
-- url     : https://prove2.me/submissions/97cdfd27-c549-4414-a4e5-0ca508551173

module
public import Definitions.Def_FltRegular_NumberTheory_SystemOfUnits
public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
public import Mathlib.RingTheory.Henselian
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
public import Mathlib.LinearAlgebra.Dimension.Torsion.Basic
public import Definitions.Def_FltRegular_NumberTheory_Hilbert92

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
variable
    [Algebra k K] (hKL : finrank k K = p) (σ : K ≃ₐ[k] K)
    (hσ : ∀ x, x ∈ Subgroup.zpowers σ)
theorem _root_.solution
    [IsGalois k K] [FiniteDimensional k K]
    (σ : K ≃ₐ[k] K) (hσ : ∀ x, x ∈ Subgroup.zpowers σ) (η : K) :
    algebraMap k K (Algebra.norm k η) = (∏ i ∈ Finset.range (orderOf σ), (σ ^ i) η) := by
  let _ : Fintype (Subgroup.zpowers σ) := inferInstance
  rw [Algebra.norm_eq_prod_automorphisms, ← Fin.prod_univ_eq_prod_range,
    ← (finEquivZPowers <| isOfFinOrder_of_finite _).symm.prod_comp]
  simp only [pow_finEquivZPowers_symm_apply]
  rw [prod_subtype]
  simp [hσ]
