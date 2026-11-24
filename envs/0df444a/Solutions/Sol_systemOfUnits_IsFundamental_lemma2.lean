-- Prove2me | solution 1 for systemOfUnits.IsFundamental.lemma2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:44:14.575827+00:00
-- url     : https://prove2.me/submissions/560d0f19-71d2-4915-ac02-000151efff43

module
public import Definitions.Def_FltRegular_NumberTheory_SystemOfUnits
public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
public import Mathlib.RingTheory.Henselian
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
public import Mathlib.LinearAlgebra.Dimension.Torsion.Basic
public import Definitions.Def_FltRegular_NumberTheory_Hilbert92
public import Theorems.Thm_systemOfUnits_isMaximal
public import Theorems.Thm_P2M_systemOfUnits_IsFundamental_maximal__0f3d3a4f4496
public import Theorems.Thm_CyclotomicIntegers_not_isUnit_one_sub_zeta
public import Theorems.Thm_CyclotomicIntegers_one_sub_zeta_mem_nonZeroDivisors


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
theorem _root_.solution [Module A G] (S : systemOfUnits p G s) (hs : S.IsFundamental)
    (i : Fin s) (a : Fin s →₀ A) (ha : a i = 1) :
    ∀ g : G, (1 - zeta p) • g ≠ Finsupp.linearCombination A S.units a := by
  let := hs.choose
  intro g hg
  have := Fact.mk hp
  let S' : systemOfUnits p G s := ⟨Function.update S.units i g,
    LinearIndependent.update S.linearIndependent i g ⟨_,
      CyclotomicIntegers.one_sub_zeta_mem_nonZeroDivisors p, a, ha ▸ one_mem A⁰, hg⟩⟩
  have ha' : Finsupp.linearCombination A S'.units (a.erase i) + S.units i =
      (1 - zeta p) • g := by
    have he : Finsupp.linearCombination A S'.units (a.erase i) =
        Finsupp.linearCombination A S.units (a.erase i) := by
      apply Finsupp.sum_congr
      intro j hj
      have hji : j ≠ i := by
        rintro rfl
        simp at hj
      change (a.erase i) j • Function.update S.units i g j = (a.erase i) j • S.units j
      rw [Function.update_of_ne hji]
    calc
      _ = Finsupp.linearCombination A S.units (a.erase i) + a i • S.units i := by
        rw [he, ha, one_smul]
      _ = Finsupp.linearCombination A S.units (a.erase i + Finsupp.single i (a i)) := by
        rw [map_add, Finsupp.linearCombination_single]
      _ = _ := by rw [Finsupp.erase_add_single, ← hg]
  have := S'.isMaximal p hp G hf
  suffices Submodule.span A (Set.range S.units) < Submodule.span A (Set.range S'.units) by
    exact (hs.maximal' _ _ _ S').not_gt <| AddSubgroup.index_strictAnti ‹_›
  suffices Submodule.span A (Set.range S.units) ≤ Submodule.span A (Set.range S'.units) ∧
      ∃ x ∈ Submodule.span A (Set.range S'.units), x ∉ Submodule.span A (Set.range S.units) by
    rcases this with ⟨hle, x, hxQ, hxP⟩
    exact lt_of_le_of_ne hle (fun heq => hxP (heq ▸ hxQ))
  constructor
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    by_cases hij : i = j
    · rw [add_comm, ← eq_sub_iff_add_eq] at ha'
      rw [← hij, ha']
      apply sub_mem
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, Function.update_self _ _ _⟩)
      · rw [← Finsupp.range_linearCombination]
        exact ⟨_, rfl⟩
    · exact Submodule.subset_span ⟨j, Function.update_of_ne (Ne.symm hij) _ _⟩
  · refine ⟨g, Submodule.subset_span ⟨i, Function.update_self _ _ _⟩, ?_⟩
    rw [← Finsupp.range_linearCombination]
    rintro ⟨l, rfl⟩
    let _ := (Algebra.id A).toModule
    let _ : SMulZeroClass A A := SMulWithZero.toSMulZeroClass
    let _ : Module A (Fin s →₀ A) := Finsupp.module (Fin s) A
    rw [← LinearMap.map_smul, ← sub_eq_zero,
      ← (Finsupp.linearCombination A S.units).map_sub] at hg
    have := DFunLike.congr_fun (linearIndependent_iff.mp S.linearIndependent _ hg) i
    simp only [Finsupp.coe_sub, Finsupp.coe_smul, ha, Pi.sub_apply, Finsupp.coe_zero,
      Pi.zero_apply, sub_eq_zero] at this
    exact CyclotomicIntegers.not_isUnit_one_sub_zeta p
      (IsUnit.of_mul_eq_one _ this)
end systemOfUnits.IsFundamental
