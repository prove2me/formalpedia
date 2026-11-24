-- Prove2me | solution 1 for finrank_G
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:44:12.835921+00:00
-- url     : https://prove2.me/submissions/900e1b39-0607-4242-93cb-777b1f6bdfe7

module
public import Definitions.Def_FltRegular_NumberTheory_SystemOfUnits
public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
public import Mathlib.RingTheory.Henselian
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
public import Mathlib.LinearAlgebra.Dimension.Torsion.Basic
public import Definitions.Def_FltRegular_NumberTheory_Hilbert92
public import Theorems.Thm_NumberField_Units_rank_of_isUnramified

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
variable [NumberField K]
variable [IsGalois k K]
attribute [local instance] _p2m_local_instance_fee6646a52_507
attribute [local instance] _p2m_local_instance_fee6646a52_512
attribute [local instance] _p2m_local_instance_fee6646a52_515
variable [IsUnramifiedAtInfinitePlaces k K]
theorem _root_.solution : finrank ℤ G = (Units.rank k + 1) * (↑p - 1) := by
  refine finrank_quotient_torsion_eq.trans ?_
  change finrank ℤ (Additive (𝓞 K)ˣ ⧸ AddSubgroup.toIntSubmodule (Subgroup.toAddSubgroup
    (MonoidHom.range <| Units.map (algebraMap (𝓞 k) (𝓞 K) : (𝓞 k) →* (𝓞 K))))) = _
  rw [Submodule.finrank_quotient]
  change _ - finrank ℤ (LinearMap.range <| AddMonoidHom.toIntLinearMap <|
    MonoidHom.toAdditive <| Units.map (algebraMap (𝓞 k) (𝓞 K) : (𝓞 k) →* (𝓞 K))) = _
  rw [LinearMap.finrank_range_of_inj, NumberField.Units.finrank_eq, NumberField.Units.finrank_eq,
    NumberField.Units.rank_of_isUnramified (k := k), add_mul, one_mul, mul_tsub, mul_one, mul_comm,
      add_tsub_assoc_of_le, tsub_add_eq_add_tsub, hKL]
  · exact (mul_one _).symm.trans_le (Nat.mul_le_mul_left _ hp.one_lt.le)
  · exact hKL ▸ hp.one_lt.le
  · intros i j e
    exact Additive.toMul.injective <| Units.ext <| Subtype.ext <| (algebraMap k K).injective <|
      congr_arg (fun i : Additive (𝓞 K)ˣ ↦ (↑(↑(Additive.toMul i) : 𝓞 K) : K)) e
