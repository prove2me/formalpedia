-- Prove2me | solution 1 for quotient_zero_sub_one_comp_aut
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:33:05.123102+00:00
-- url     : https://prove2.me/submissions/e212a23d-3f93-47c1-8e48-6e5b4b886c75

module
public import Mathlib.RingTheory.NormTrace
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits
public import Definitions.Def_FltRegular_NumberTheory_Cyclotomic_MoreLemmas

set_option autoImplicit false
@[expose] public section
public section
variable {K : Type*} {p : ℕ} [hpri : Fact p.Prime] [Field K] [CharZero K]
  [IsCyclotomicExtension {p} ℚ K]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ p)
open scoped nonZeroDivisors NumberField
open Polynomial IsCyclotomicExtension.Rat
variable (hp : p ≠ 2)
theorem _root_.solution (σ : 𝓞 K →+* 𝓞 K) :
    (Ideal.Quotient.mk (Ideal.span {(hζ.toInteger : 𝓞 K) - 1})).comp σ =
      Ideal.Quotient.mk _ := by
  let _ := IsCyclotomicExtension.numberField {p} ℚ K
  let : AddGroup (𝓞 K ⧸ Ideal.span (singleton (hζ.toInteger - 1 : 𝓞 K))) := inferInstance
  apply RingHom.toIntAlgHom_injective
  apply hζ.integralPowerBasis.algHom_ext
  have hgen : hζ.integralPowerBasis.gen = hζ.toInteger := by
    simp only [IsPrimitiveRoot.integralPowerBasis_gen]
  rw [hgen]
  simp only [RingHom.toIntAlgHom, AlgHom.coe_mk, RingHom.coe_comp, Function.comp_apply]
  rw [← sub_eq_zero, ← Ideal.Quotient.mk_eq_mk, ← Ideal.Quotient.mk_eq_mk,
    ← Submodule.Quotient.mk_sub, Ideal.Quotient.mk_eq_mk, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton]
  apply hζ.toInteger_isPrimitiveRoot.sub_one_dvd_sub hpri.out
  · rw [mem_nthRootsFinset (NeZero.pos p), ← map_pow]
    change σ (hζ.toInteger ^ p) = 1
    rw [hζ.toInteger_isPrimitiveRoot.pow_eq_one, map_one]
  · rw [mem_nthRootsFinset (NeZero.pos p)]
    exact hζ.toInteger_isPrimitiveRoot.pow_eq_one
