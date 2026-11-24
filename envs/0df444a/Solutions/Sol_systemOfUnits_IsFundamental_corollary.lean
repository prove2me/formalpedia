-- Prove2me | solution 1 for systemOfUnits.IsFundamental.corollary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:45:23.066236+00:00
-- url     : https://prove2.me/submissions/c78f9277-745a-4a40-9b88-02e8ef4e9d0e

module
public import Definitions.Def_FltRegular_NumberTheory_SystemOfUnits
public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
public import Mathlib.RingTheory.Henselian
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
public import Mathlib.LinearAlgebra.Dimension.Torsion.Basic
public import Definitions.Def_FltRegular_NumberTheory_Hilbert92
public import Theorems.Thm_systemOfUnits_IsFundamental_lemma2
public import Theorems.Thm_CyclotomicIntegers_isCoprime_one_sub_zeta


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
theorem _root_.solution [Module A G] (S : systemOfUnits p G s) (hs : S.IsFundamental) (a : Fin s → ℤ)
    (ha : ∃ i, ¬ (p : ℤ) ∣ a i) :
    ∀ g : G, (1 - zeta p) • g ≠ ∑ i, a i • S.units i := by
  intro g hg
  obtain ⟨i, hi⟩ := ha
  have := Fact.mk hp
  obtain ⟨x, y, e⟩ := CyclotomicIntegers.isCoprime_one_sub_zeta p (a i) hi
  let b' : Fin s → A := fun j ↦ x * (1 - zeta ↑p) + y * (a j)
  let b := Finsupp.ofSupportFinite b' (Set.toFinite (Function.support _))
  have hb : b i = 1 := by
    rw [← e]
    rfl
  apply lemma2 p hp G s hf S hs i b hb (x • ∑ i, S.units i + y • g)
  rw [smul_add, smul_smul _ y, mul_comm, ← smul_smul, hg, smul_sum, smul_sum, smul_sum,
    ← sum_add_distrib, Finsupp.linearCombination_apply, Finsupp.sum_fintype]
  · congr
    · ext j
      simp only [smul_smul, Finsupp.ofSupportFinite_coe, add_smul, b', b]
      congr 1
      · rw [mul_comm]
      · rw [← Int.cast_smul_eq_zsmul (R := A), smul_smul]
  · simp
end systemOfUnits.IsFundamental
