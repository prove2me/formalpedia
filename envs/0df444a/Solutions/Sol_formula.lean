-- Prove2me | solution 1 for formula
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:16:06.84328+00:00
-- url     : https://prove2.me/submissions/fec419b9-7562-45e8-a73d-beec507d9cec

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
public import Theorems.Thm_x_plus_y_mul_ne_zero
public import Theorems.Thm_associated_eta_zero_unit_spec

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
theorem _root_.solution (η₁) (hη₁ : η₁ ≠ η₀) (η₂) (hη₂ : η₂ ≠ η₀) :
    (η₂ - η₀ : 𝓞 K) * ε η₁ hη₁ * (α η₁ hη₁ * β η₂ hη₂) ^ p +
      (η₀ - η₁) * ε η₂ hη₂ * (α η₂ hη₂ * β η₁ hη₁) ^ p =
      (η₂ - η₁) * (π ^ m * (β η₁ hη₁ * β η₂ hη₂)) ^ p := by
  rw [← mul_right_inj' (x_plus_y_mul_ne_zero hp hζ e hz η₀), mul_add]
  simp_rw [mul_left_comm (x + y * η₀), mul_pow, mul_assoc,
    mul_left_comm (η₂ - η₀ : 𝓞 K), mul_left_comm (η₀ - η₁ : 𝓞 K), ← mul_assoc,
    associated_eta_zero_unit_spec, mul_assoc, ← mul_left_comm (η₂ - η₀ : 𝓞 K),
    ← mul_left_comm (η₀ - η₁ : 𝓞 K), pow_mul, ← mul_pow, mul_comm (β η₂ hη₂),
    ← mul_assoc]
  rw [← add_mul]
  congr 1
  ring
