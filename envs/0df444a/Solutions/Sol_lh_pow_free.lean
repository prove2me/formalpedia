-- Prove2me | solution 1 for lh_pow_free
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:45:02.539261+00:00
-- url     : https://prove2.me/submissions/ca0534d4-c7a3-42a1-ba64-5f11c393336a

module
public import Definitions.Def_FltRegular_NumberTheory_SystemOfUnits
public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
public import Mathlib.RingTheory.Henselian
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
public import Mathlib.LinearAlgebra.Dimension.Torsion.Basic
public import Definitions.Def_FltRegular_NumberTheory_Hilbert92
public import Theorems.Thm_P2M_lh_pow_free__ffcdb6e15d31

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
local notation "G" =>
  Additive (relativeUnitsWithGenerator p hp hKL σ hσ) ⧸
    AddCommGroup.torsion (Additive (relativeUnitsWithGenerator p hp hKL σ hσ))
local notation "mkG" => unitToU p hp hKL σ hσ
variable [NumberField k]
include hp
theorem _root_.solution (ν : (𝓞 k)ˣ)
    (hk : ∀ (ε : (𝓞 k)ˣ) (n : ℕ), ε ^ (p ^ n) = 1 → ∃ i, ν ^ i = ε)
    (η : Fin (NumberField.Units.rank k + 2) → Additive (𝓞 k)ˣ) :
    ∃ (a : ℤ) (ι : Fin (NumberField.Units.rank k + 2) → ℤ)
      (i₀ : Fin (NumberField.Units.rank k + 2)),
      ∑ i, ι i • η i = (a * p) • Additive.ofMul ν ∧
        ¬ (p : ℤ) ∣ ι i₀ ∧ (ν = 1 → i₀ ≠ Fin.last _) := by
  convert lh_pow_free' p hp ν hk _ ?_ η
  · simp [Fin.ext_iff]
  · rw [NumberField.Units.finrank_eq]
    exact Nat.lt_add_one _
