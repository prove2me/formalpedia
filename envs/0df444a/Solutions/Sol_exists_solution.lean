-- Prove2me | solution 1 for exists_solution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:17:25.346049+00:00
-- url     : https://prove2.me/submissions/0efa02ee-0522-49e5-bc13-5505509abcea

module
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits
public import Mathlib.RingTheory.ClassGroup.Basic
public import Definitions.Def_FltRegular_CaseII_AuxLemmas
public import Definitions.Def_FltRegular_NumberTheory_Cyclotomic_MoreLemmas
public import Definitions.Def_FltRegular_NumberTheory_Cyclotomic_UnitLemmas
public import Definitions.Def_FltRegular_NumberTheory_KummersLemma_KummersLemma
public import Definitions.Def_FltRegular_CaseII_InductionStep
public import Theorems.Thm_a_div_a_zero_num_spec
public import Theorems.Thm_formula

set_option autoImplicit false
@[expose] public section
public section
open scoped nonZeroDivisors NumberField
open Polynomial IsCyclotomicExtension.Rat
attribute [local implicit_reducible] integralClosure NumberField.RingOfIntegers
variable {K : Type} {p : ℕ} [NeZero p] [Field K] [NumberField K] (hp : p ≠ 2)
variable {ζ : K} (hζ : IsPrimitiveRoot ζ p) {x y z : 𝓞 K} {ε : (𝓞 K)ˣ}
local notation3 "π" => hζ.toInteger - 1
local notation3 "𝔭" => Ideal.span {π}
local notation3 "𝔦" η => Ideal.span {(x + y * η : 𝓞 K)}
local notation3 "𝔵" => Ideal.span {x}
local notation3 "𝔶" => Ideal.span {y}
local notation3 "𝔷" => Ideal.span {z}
variable {m : ℕ} (e : x ^ p + y ^ p = ε * ((hζ.toInteger - 1) ^ (m + 1) * z) ^ p)
variable (hy : ¬ hζ.toInteger - 1 ∣ y) (hz : ¬ hζ.toInteger - 1 ∣ z)
variable (η : nthRootsFinset p (1 : 𝓞 K))
local notation3 "𝔪" => gcd 𝔵 𝔶
variable [hpri : Fact p.Prime]
variable [IsCyclotomicExtension {p} ℚ K]
local notation "𝔠" => fun η ↦ divZetaSubOneDvdGcd hp hζ e hy η
local notation "𝔷'" => zDivM hζ e hy
local notation "𝔞" => rootDivZetaSubOneDvdGcd hp hζ e hy
local notation "η₀" => zetaSubOneDvdRoot hp hζ e hy
local notation "𝔞₀" => aEtaZeroDvdPPow hp hζ e hy
variable [Fintype (ClassGroup (𝓞 K))] (hreg : p.Coprime <| Fintype.card <| ClassGroup (𝓞 K))
local notation "α" => fun η ↦ aDivAZeroNum hp hζ e hy hz η hreg
local notation "β" => fun η ↦ aDivAZeroDenom hp hζ e hy hz η hreg
local notation "ε" => fun η ↦ associatedEtaZeroUnit hp hζ e hy hz η hreg
include hreg e hy hz hp
theorem _root_.solution :
    ∃ (x' y' z' : 𝓞 K) (ε₁ ε₂ ε₃ : (𝓞 K)ˣ), ¬ π ∣ x' ∧ ¬ π ∣ y' ∧
      ¬ π ∣ z' ∧ ε₁ * x' ^ p + ε₂ * y' ^ p = ε₃ * (π ^ m * z') ^ p := by
  have h₁ :=
    mul_mem_nthRootsFinset (η₀ : _).prop
      (hζ.toInteger_isPrimitiveRoot.mem_nthRootsFinset hpri.out.pos)
  rw [one_mul] at h₁
  let η₁ : nthRootsFinset p (1 : 𝓞 K) := ⟨η₀ * hζ.toInteger, h₁⟩
  have h₂ :=
    mul_mem_nthRootsFinset (η₁ : _).prop
      (hζ.toInteger_isPrimitiveRoot.mem_nthRootsFinset hpri.out.pos)
  rw [one_mul] at h₂
  let η₂ : nthRootsFinset p (1 : 𝓞 K) := ⟨η₀ * hζ.toInteger * hζ.toInteger, h₂⟩
  have hη₁ : η₁ ≠ η₀ := by
    rw [← Subtype.coe_injective.ne_iff]
    change (η₀ * hζ.toInteger : 𝓞 K) ≠ η₀
    rw [Ne, mul_right_eq_self₀, not_or]
    exact ⟨hζ.toInteger_isPrimitiveRoot.ne_one hpri.out.one_lt,
      ne_zero_of_mem_nthRootsFinset one_ne_zero (η₀ : _).prop⟩
  have hη₂ : η₂ ≠ η₀ := by
    rw [← Subtype.coe_injective.ne_iff]
    change (η₀ * hζ.toInteger * hζ.toInteger : 𝓞 K) ≠ η₀
    rw [Ne, mul_assoc, ← pow_two, mul_right_eq_self₀, not_or]
    exact ⟨hζ.toInteger_isPrimitiveRoot.pow_ne_one_of_pos_of_lt (by lia)
      (hpri.out.two_le.lt_or_eq.resolve_right hp.symm),
      ne_zero_of_mem_nthRootsFinset one_ne_zero (η₀ : _).prop⟩
  have hη : η₂ ≠ η₁ := by
    rw [← Subtype.coe_injective.ne_iff]
    change (η₀ * hζ.toInteger * hζ.toInteger : 𝓞 K) ≠ η₀ * hζ.toInteger
    rw [Ne, mul_right_eq_self₀, not_or]
    exact ⟨hζ.toInteger_isPrimitiveRoot.ne_one hpri.out.one_lt,
      mul_ne_zero (ne_zero_of_mem_nthRootsFinset one_ne_zero (η₀ : _).prop)
        (hζ.toInteger_isPrimitiveRoot.ne_zero hpri.out.ne_zero)⟩
  obtain ⟨u₁, hu₁⟩ :=
    hζ.toInteger_isPrimitiveRoot.nthRootsFinset_pairwise_associated_sub_one_sub_of_prime
      hpri.out η₂.prop (η₀ : _).prop (Subtype.coe_injective.ne_iff.mpr hη₂)
  obtain ⟨u₂, hu₂⟩ :=
    hζ.toInteger_isPrimitiveRoot.nthRootsFinset_pairwise_associated_sub_one_sub_of_prime hpri.out
      (η₀ : _).prop η₁.prop (Subtype.coe_injective.ne_iff.mpr hη₁.symm)
  obtain ⟨u₃, hu₃⟩ :=
    hζ.toInteger_isPrimitiveRoot.nthRootsFinset_pairwise_associated_sub_one_sub_of_prime
      hpri.out η₂.prop (η₁ : _).prop (Subtype.coe_injective.ne_iff.mpr hη)
  have := formula hp hζ e hy hz hreg η₁ hη₁ η₂ hη₂
  rw [← hu₁, ← hu₂, ← hu₃, mul_assoc _ (u₁ : 𝓞 K), mul_assoc _ (u₂ : 𝓞 K),
    mul_assoc _ (u₃ : 𝓞 K), mul_assoc (π), mul_assoc (π), ← mul_add,
    mul_right_inj' (hζ.toInteger_isPrimitiveRoot.sub_one_ne_zero hpri.out.one_lt),
    ← Units.val_mul, ← Units.val_mul] at this
  refine ⟨_, _, _, _, _, _, ?_, ?_, ?_, this⟩
  · exact hζ.zeta_sub_one_prime'.not_dvd_mul
      (a_div_a_zero_num_spec hp hζ e hy hz η₁ hreg hη₁)
      (a_div_a_zero_denom_spec hp hζ e hy hz η₂ hreg hη₂)
  · exact hζ.zeta_sub_one_prime'.not_dvd_mul
      (a_div_a_zero_num_spec hp hζ e hy hz η₂ hreg hη₂)
      (a_div_a_zero_denom_spec hp hζ e hy hz η₁ hreg hη₁)
  · exact hζ.zeta_sub_one_prime'.not_dvd_mul
      (a_div_a_zero_denom_spec hp hζ e hy hz η₁ hreg hη₁)
      (a_div_a_zero_denom_spec hp hζ e hy hz η₂ hreg hη₂)
