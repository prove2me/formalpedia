-- Prove2me | solution 1 for lh_pow_free_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:43:07.932884+00:00
-- url     : https://prove2.me/submissions/f8c2cb68-e016-4951-b95d-dddd5c22de19

module
public import Definitions.Def_FltRegular_NumberTheory_SystemOfUnits
public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
public import Mathlib.RingTheory.Henselian
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
public import Mathlib.LinearAlgebra.Dimension.Torsion.Basic
public import Definitions.Def_FltRegular_NumberTheory_Hilbert92
public import Theorems.Thm_exists_pow_smul_eq_and_not_dvd

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
theorem _root_.solution {M} [CommGroup M] [Module.Finite ℤ (Additive M)] (ν : M)
    (hk : ∀ (ε : M) (n : ℕ), ε ^ (p ^ n) = 1 → ∃ i, ν ^ i = ε)
    (r) (hr : finrank ℤ (Additive M) < r) (η : Fin r → Additive M) :
    ∃ (a : ℤ) (ι : Fin r → ℤ) (i : Fin r),
      ∑ i, ι i • η i = a • (Additive.ofMul ν) ∧ ¬ ↑p ∣ ι i := by
  obtain ⟨f, hf, hf'⟩ := Fintype.not_linearIndependent_iff.mp
    (mt (LinearIndependent.fintype_card_le_finrank (R := ℤ) (b := η))
      ((hr.trans_eq (Fintype.card_fin r).symm).not_ge))
  obtain ⟨n, f', hf', i, hi⟩ := exists_pow_smul_eq_and_not_dvd f
    (Function.ne_iff.mpr hf') p hp.ne_one
  simp_rw [hf', Pi.smul_apply, smul_assoc, ← smul_sum] at hf
  obtain ⟨a, ha⟩ := hk _ _ hf
  rw [← zpow_natCast] at ha
  exact ⟨a, f', i, ha.symm, hi⟩
