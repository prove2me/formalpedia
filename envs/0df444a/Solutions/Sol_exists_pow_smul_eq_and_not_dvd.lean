-- Prove2me | solution 1 for exists_pow_smul_eq_and_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:42:21.632318+00:00
-- url     : https://prove2.me/submissions/177dc0e4-bba8-426c-b4de-a172315d439f

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
local notation "G" =>
  Additive (relativeUnitsWithGenerator p hp hKL σ hσ) ⧸
    AddCommGroup.torsion (Additive (relativeUnitsWithGenerator p hp hKL σ hσ))
local notation "mkG" => unitToU p hp hKL σ hσ
variable [NumberField k]
open Finset
theorem _root_.solution
    {ι : Type*} [Finite ι] (f : ι → ℤ) (hf : f ≠ 0) (p : ℕ) (hp : p ≠ 1) :
    ∃ (n : ℕ) (f' : ι → ℤ), (f = p ^ n • f') ∧ ∃ i, ¬ ↑p ∣ f' i := by
  cases nonempty_fintype ι
  have : (univ.filter (fun i ↦ f i ≠ 0)).Nonempty := by
    by_contra h
    exact hf (funext <| by simpa [filter_eq_empty_iff] using h)
  obtain ⟨i, hfi, hi⟩ := exists_min_image _ (padicValInt p ∘ f) this
  replace hfi : f i ≠ 0 := by simpa using hfi
  let n := padicValInt p (f i)
  have : ∀ j, (p : ℤ) ^ n ∣ f j := fun j ↦ if h : f j = 0 then h ▸ dvd_zero _ else
    (pow_dvd_pow _ (hi _ (mem_filter.mpr ⟨mem_univ j, h⟩))).trans (padicValInt_dvd _)
  simp_rw [← Nat.cast_pow] at this
  choose f' hf' using this
  use n, f', funext hf', i
  intro hi
  have : (p : ℤ) ^ (n + 1) ∣ f i := by
    rw [hf', pow_succ, Nat.cast_pow]
    exact _root_.mul_dvd_mul_left _ hi
  simp only [padicValInt_dvd_iff_of_ne_one hp, hfi, false_or] at this
  lia
