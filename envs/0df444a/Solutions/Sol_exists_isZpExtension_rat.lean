-- Prove2me | solution 1 for exists_isZpExtension_rat
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T20:26:31.088054+00:00
-- url     : https://prove2.me/submissions/b3cf4489-1c24-48f7-ab31-e505a94b4312

import Theorems.Thm_PadicInt_nonempty_continuousMulEquiv_principalUnits
import Theorems.Thm_cyclotomicCharacter_algebraicClosure_rat_surjective
import Theorems.Thm_InfiniteGalois_nonempty_continuousMulEquiv_fixedField_ker
import Definitions.Def_ZpExtension
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

open IntermediateField in
theorem solution (p : ℕ) [Fact p.Prime] (hp : Odd p) :
    ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), IsZpExtension p ℚ L := by
  have hp2 : p ≠ 2 := by rintro rfl; exact (Nat.not_even_iff_odd.2 hp) even_two
  obtain ⟨Φ⟩ := PadicInt.nonempty_continuousMulEquiv_principalUnits p hp2
  set U := (Units.map (PadicInt.toZMod (p := p)).toMonoidHom).ker
  let q : ℤ_[p]ˣ →* U := (powMonoidHom (p - 1)).codRestrict U (fun u ↦ by
    rw [MonoidHom.mem_ker, powMonoidHom_apply, map_pow]
    exact ZMod.units_pow_card_sub_one_eq_one p _)
  let ψ : ℤ_[p]ˣ →* Multiplicative ℤ_[p] := Φ.toMulEquiv.toMonoidHom.comp q
  have hψc : Continuous ψ :=
    Φ.continuous.comp ((continuous_pow (p - 1)).subtype_mk _)
  have hψs : Function.Surjective ψ := by
    intro b
    obtain ⟨c, hc⟩ : IsUnit ((p - 1 : ℕ) : ℤ_[p]) := PadicInt.isUnit_iff.2 PadicInt.norm_natCast_p_sub_one
    let v : U := Φ.symm (Multiplicative.ofAdd ((c⁻¹ : ℤ_[p]ˣ) * b.toAdd))
    refine ⟨(v : ℤ_[p]ˣ), ?_⟩
    have hq : q v = v ^ (p - 1) := Subtype.ext rfl
    show Φ (q v) = b
    rw [hq, map_pow, ContinuousMulEquiv.apply_symm_apply]
    rw [← ofAdd_nsmul, nsmul_eq_mul, ← hc, ← mul_assoc, Units.mul_inv, one_mul]
    rfl
  have : IsAlgClosure ℚ (AlgebraicClosure ℚ) := by
    convert AlgebraicClosure.instIsAlgClosure ℚ
    · rfl
    · exact Subsingleton.elim _ _
  have : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)
  have : IsGalois ℚ (AlgebraicClosure ℚ) := IsGalois.mk
  let χ := (cyclotomicCharacter (AlgebraicClosure ℚ) p).comp
      (MulSemiringAction.toRingAut Gal(AlgebraicClosure ℚ/ℚ) (AlgebraicClosure ℚ))
  have hχc : Continuous χ := cyclotomicCharacter.continuous p ℚ (AlgebraicClosure ℚ)
  have hχs : Function.Surjective χ := cyclotomicCharacter_algebraicClosure_rat_surjective p
  obtain ⟨hG, hΓ⟩ := InfiniteGalois.nonempty_continuousMulEquiv_fixedField_ker (ψ.comp χ) (hψc.comp hχc) (hψs.comp hχs)
  exact ⟨fixedField (ψ.comp χ).ker, hG, hΓ⟩
