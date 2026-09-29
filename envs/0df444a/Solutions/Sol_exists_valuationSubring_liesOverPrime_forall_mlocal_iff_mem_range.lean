-- Prove2me | solution 1 for exists_valuationSubring_liesOverPrime_forall_mlocal_iff_mem_range
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/951a2934-eecb-508f-849b-a0c3c4ef8d1d

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_exists_valuationSubring_liesOverPrime_forall_mlocal_iff_mem_range

set_option autoImplicit false

namespace Bridge

open Polynomial

abbrev Kb : Type := AlgebraicClosure ℚ

abbrev Ob : Type := ↥(integralClosure ℤ Kb)

abbrev ZBar : Type := ↥(integralClosure ℤ ℂ)

section image

variable (ι : Kb →+* ℂ)

theorem exists_eq_of_isAlgebraic {z : ℂ} (hz : IsAlgebraic ℚ z) : ∃ a : Kb, ι a = z := by
  obtain ⟨q, hq0, hqz⟩ := hz
  have hsplit : (q.map (algebraMap ℚ Kb)).Splits := IsAlgClosed.splits _
  have himg := Polynomial.Splits.image_rootSet hsplit ι.toRatAlgHom
  have hzmem : z ∈ q.rootSet ℂ := by
    rw [Polynomial.mem_rootSet]
    exact ⟨hq0, hqz⟩
  rw [← himg] at hzmem
  obtain ⟨a, -, ha⟩ := hzmem
  exact ⟨a, ha⟩

theorem isIntegral_iff (a : Kb) : IsIntegral ℤ (ι a) ↔ IsIntegral ℤ a := by
  have hcomp : algebraMap ℤ ℂ = ι.comp (algebraMap ℤ Kb) := RingHom.ext_int _ _
  constructor
  · rintro ⟨f, hf, hfa⟩
    refine ⟨f, hf, ι.injective ?_⟩
    rw [Polynomial.hom_eval₂, map_zero, ← hcomp, hfa]
  · rintro ⟨f, hf, hfa⟩
    refine ⟨f, hf, ?_⟩
    rw [hcomp, ← Polynomial.hom_eval₂, hfa, map_zero]

theorem isIntegral_int_map {A B : Type*} [CommRing A] [CommRing B] [Algebra ℤ A] [Algebra ℤ B]
    (φ : A →+* B) {x : A} (hx : IsIntegral ℤ x) : IsIntegral ℤ (φ x) := by
  obtain ⟨f, hf, hfx⟩ := hx
  refine ⟨f, hf, ?_⟩
  rw [show algebraMap ℤ B = φ.comp (algebraMap ℤ A) from RingHom.ext_int _ _, ← Polynomial.hom_eval₂, hfx,
    map_zero]

theorem exists_eq_of_mem_ZBar (x : ZBar) : ∃ a : Ob, ι (a : Kb) = (x : ℂ) := by
  have hx : IsIntegral ℤ (x : ℂ) := (mem_integralClosure_iff ℤ ℂ).mp x.2
  have halg : IsAlgebraic ℚ (x : ℂ) := (hx.tower_top (A := ℚ)).isAlgebraic
  obtain ⟨a, ha⟩ := exists_eq_of_isAlgebraic ι halg
  have hai : IsIntegral ℤ a := by
    rw [← isIntegral_iff ι, ha]
    exact hx
  exact ⟨⟨a, (mem_integralClosure_iff ℤ Kb).mpr hai⟩, ha⟩

noncomputable def psi : Ob →+* ZBar :=
  (ι.comp (integralClosure ℤ Kb).val.toRingHom).codRestrict (integralClosure ℤ ℂ) fun x =>
    (mem_integralClosure_iff ℤ ℂ).mpr ((isIntegral_iff ι (x : Kb)).mpr ((mem_integralClosure_iff ℤ Kb).mp x.2))

@[scoped simp] theorem coe_psi (x : Ob) : (psi ι x : ℂ) = ι (x : Kb) := rfl

theorem psi_surjective : Function.Surjective (psi ι) := by
  intro x
  obtain ⟨a, ha⟩ := exists_eq_of_mem_ZBar ι x
  exact ⟨a, Subtype.ext ha⟩

end image

section local_ring

variable (𝔫 : Ideal Ob)

def IsNLocal (a : Kb) : Prop := ∃ x y : Ob, y ∉ 𝔫 ∧ (x : Kb) = y * a

variable {𝔫}

theorem isNLocal_of_mem (h1 : (1 : Ob) ∉ 𝔫) (x : Ob) : IsNLocal 𝔫 (x : Kb) :=
  ⟨x, 1, h1, by simp⟩

theorem IsNLocal.mul (h𝔫 : 𝔫.IsPrime) {a b : Kb} (ha : IsNLocal 𝔫 a) (hb : IsNLocal 𝔫 b) :
    IsNLocal 𝔫 (a * b) := by
  obtain ⟨x, y, hy, e⟩ := ha
  obtain ⟨x', y', hy', e'⟩ := hb
  refine ⟨x * x', y * y', fun h => (h𝔫.mem_or_mem h).elim hy hy', ?_⟩
  push_cast
  rw [e, e']
  ring

theorem IsNLocal.add (h𝔫 : 𝔫.IsPrime) {a b : Kb} (ha : IsNLocal 𝔫 a) (hb : IsNLocal 𝔫 b) :
    IsNLocal 𝔫 (a + b) := by
  obtain ⟨x, y, hy, e⟩ := ha
  obtain ⟨x', y', hy', e'⟩ := hb
  refine ⟨x * y' + x' * y, y * y', fun h => (h𝔫.mem_or_mem h).elim hy hy', ?_⟩
  push_cast
  rw [e, e']
  ring

theorem IsNLocal.neg {a : Kb} (ha : IsNLocal 𝔫 a) : IsNLocal 𝔫 (-a) := by
  obtain ⟨x, y, hy, e⟩ := ha
  exact ⟨-x, y, hy, by push_cast; rw [e]; ring⟩

theorem isNLocal_or_isNLocal_inv (h𝔫 : 𝔫.IsPrime) (p : ℕ) [Fact p.Prime] (hp : (p : Ob) ∈ 𝔫) (a : Kb) :
    IsNLocal 𝔫 a ∨ IsNLocal 𝔫 a⁻¹ := by
  classical
  haveI : Algebra.IsAlgebraic ℚ Kb := AlgebraicClosure.isAlgebraic ℚ
  have haint : IsIntegral ℚ a := (Algebra.IsAlgebraic.isAlgebraic a).isIntegral

  let F : IntermediateField ℚ Kb := IntermediateField.adjoin ℚ {a}
  haveI : FiniteDimensional ℚ F := IntermediateField.adjoin.finiteDimensional haint
  haveI : NumberField F := NumberField.mk
  let aF : F := ⟨a, IntermediateField.mem_adjoin_simple_self ℚ a⟩
  have hRint : ∀ r : NumberField.RingOfIntegers F, IsIntegral ℤ (((r : F) : Kb)) := fun r =>
    isIntegral_int_map (algebraMap F Kb) (NumberField.RingOfIntegers.isIntegral_coe r)
  let ρ : NumberField.RingOfIntegers F →+* Ob :=
    ((algebraMap F Kb).comp (algebraMap (NumberField.RingOfIntegers F) F)).codRestrict (integralClosure ℤ Kb)
      fun r => (mem_integralClosure_iff ℤ Kb).mpr (hRint r)
  let 𝔭 : Ideal (NumberField.RingOfIntegers F) := 𝔫.comap ρ
  haveI h𝔭 : 𝔭.IsPrime := Ideal.comap_isPrime ρ 𝔫
  have h𝔭ne : 𝔭 ≠ ⊥ := by
    intro h
    have hpmem : (p : NumberField.RingOfIntegers F) ∈ 𝔭 := by
      show ρ (p : NumberField.RingOfIntegers F) ∈ 𝔫
      rwa [map_natCast]
    rw [h, Ideal.mem_bot] at hpmem
    exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) hpmem

  let L := Localization.AtPrime 𝔭
  haveI : IsDiscreteValuationRing L :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (NumberField.RingOfIntegers F) h𝔭ne L
  have hunit : ∀ s : 𝔭.primeCompl, IsUnit (algebraMap (NumberField.RingOfIntegers F) F s) := by
    intro s
    apply IsUnit.mk0
    intro h0
    apply s.2
    have : (s : NumberField.RingOfIntegers F) = 0 :=
      (IsFractionRing.injective (NumberField.RingOfIntegers F) F) (by rw [h0, map_zero])
    rw [this]
    exact 𝔭.zero_mem
  letI : Algebra L F := (IsLocalization.lift (M := 𝔭.primeCompl) hunit : L →+* F).toAlgebra
  haveI : IsScalarTower (NumberField.RingOfIntegers F) L F :=
    IsScalarTower.of_algebraMap_eq fun r => (IsLocalization.lift_eq (M := 𝔭.primeCompl) hunit r).symm
  haveI : IsFractionRing L F :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization 𝔭.primeCompl L F

  have key : ∀ x : F, IsLocalization.IsInteger L x → IsNLocal 𝔫 (x : Kb) := by
    intro x hx
    obtain ⟨l, hl⟩ := hx
    obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.mk'_surjective 𝔭.primeCompl l
    simp only at hrs
    have h2 := congrArg (algebraMap L F) (IsLocalization.mk'_spec L r s)
    rw [map_mul, hrs, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at h2

    refine ⟨ρ r, ρ s, s.2, ?_⟩
    have h3 := congrArg (algebraMap F Kb) h2
    rw [map_mul] at h3

    change algebraMap F Kb (algebraMap _ F r) = algebraMap F Kb (algebraMap _ F (s : NumberField.RingOfIntegers F)) * (x : Kb)
    rw [← h3, mul_comm]
    congr 1
    exact congrArg _ hl
  rcases ValuationRing.isInteger_or_isInteger L aF with h | h
  · exact Or.inl (key aF h)
  · exact Or.inr (key aF⁻¹ h)

noncomputable def valuationSubringOf (h𝔫 : 𝔫.IsPrime) (p : ℕ) [Fact p.Prime] (hp : (p : Ob) ∈ 𝔫) :
    ValuationSubring Kb where
  carrier := {a | IsNLocal 𝔫 a}
  mul_mem' ha hb := ha.mul h𝔫 hb
  one_mem' := by simpa using isNLocal_of_mem (𝔫 := 𝔫) (fun h => h𝔫.ne_top ((Ideal.eq_top_iff_one _).mpr h)) 1
  add_mem' ha hb := ha.add h𝔫 hb
  zero_mem' := by simpa using isNLocal_of_mem (𝔫 := 𝔫) (fun h => h𝔫.ne_top ((Ideal.eq_top_iff_one _).mpr h)) 0
  neg_mem' ha := ha.neg
  mem_or_inv_mem' a := isNLocal_or_isNLocal_inv h𝔫 p hp a

theorem mem_valuationSubringOf_iff (h𝔫 : 𝔫.IsPrime) (p : ℕ) [Fact p.Prime] (hp : (p : Ob) ∈ 𝔫) (a : Kb) :
    a ∈ valuationSubringOf h𝔫 p hp ↔ IsNLocal 𝔫 a := Iff.rfl

theorem liesOverPrime_valuationSubringOf (h𝔫 : 𝔫.IsPrime) (p : ℕ) [Fact p.Prime] (hp : (p : Ob) ∈ 𝔫) :
    (valuationSubringOf h𝔫 p hp).LiesOverPrime p := by
  have h1 : (1 : Ob) ∉ 𝔫 := fun h => h𝔫.ne_top ((Ideal.eq_top_iff_one _).mpr h)
  have hpA : (p : Kb) ∈ valuationSubringOf h𝔫 p hp := by
    simpa using isNLocal_of_mem (𝔫 := 𝔫) h1 (p : Ob)
  have hp0 : (p : Kb) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero

  have hpinv : (p : Kb)⁻¹ ∉ valuationSubringOf h𝔫 p hp := by
    rintro ⟨x, y, hy, e⟩
    apply hy
    have : y = x * (p : Ob) := by
      apply Subtype.ext
      push_cast
      rw [e, mul_assoc, inv_mul_cancel₀ hp0, mul_one]
    rw [this]
    exact 𝔫.mul_mem_left x hp
  show (p : Kb) ∈ (valuationSubringOf h𝔫 p hp).nonunits
  rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
  refine ⟨hpA, ?_⟩
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  rintro ⟨u, hu⟩
  apply hpinv
  have hmul : ((↑u⁻¹ : ↥(valuationSubringOf h𝔫 p hp)) : Kb) * (p : Kb) = 1 := by
    have h := congrArg (fun v : ↥(valuationSubringOf h𝔫 p hp) => (v : Kb)) u.inv_mul
    simp only [hu] at h
    simpa using h
  have hinv : ((↑u⁻¹ : ↥(valuationSubringOf h𝔫 p hp)) : Kb) = (p : Kb)⁻¹ := eq_inv_of_mul_eq_one_left hmul
  rw [← hinv]
  exact (↑u⁻¹ : ↥(valuationSubringOf h𝔫 p hp)).2

end local_ring

end Bridge
p2m_reactivate "P2MW.S_exists_valuationSubring_liesOverPrime_forall_mlocal_iff_mem_range.Bridge"

open Bridge in
theorem solution
    (p : ℕ) [Fact p.Prime] (ι : AlgebraicClosure ℚ →+* ℂ)
    (𝔪 : Ideal ↥(integralClosure ℤ ℂ)) (h𝔪 : 𝔪.IsMaximal) (hp𝔪 : (p : ↥(integralClosure ℤ ℂ)) ∈ 𝔪) :
    ∃ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p ∧
      ∀ z : ℂ, (∃ x y : ↥(integralClosure ℤ ℂ), y ∉ 𝔪 ∧ (x : ℂ) = y * z) ↔
        ∃ a : AlgebraicClosure ℚ, a ∈ A ∧ ι a = z := by
  classical
  let 𝔫 : Ideal Ob := 𝔪.comap (psi ι)
  have h𝔫 : 𝔫.IsPrime := by
    haveI := h𝔪.isPrime
    exact Ideal.comap_isPrime (psi ι) 𝔪
  have hp𝔫 : (p : Ob) ∈ 𝔫 := by
    show psi ι (p : Ob) ∈ 𝔪
    rwa [map_natCast]
  refine ⟨valuationSubringOf h𝔫 p hp𝔫, liesOverPrime_valuationSubringOf h𝔫 p hp𝔫, fun z => ⟨?_, ?_⟩⟩
  · rintro ⟨x, y, hy, e⟩
    obtain ⟨x', hx'⟩ := psi_surjective ι x
    obtain ⟨y', hy'⟩ := psi_surjective ι y
    have hy'𝔫 : y' ∉ 𝔫 := fun h => hy (hy' ▸ h)
    have hy0 : (y : ℂ) ≠ 0 := by
      intro h
      apply hy
      have : y = 0 := Subtype.ext h
      rw [this]
      exact 𝔪.zero_mem
    refine ⟨(x' : Kb) / y', ⟨x', y', hy'𝔫, ?_⟩, ?_⟩
    · have : (y' : Kb) ≠ 0 := by
        intro h
        apply hy0
        rw [← hy', coe_psi, h, map_zero]
      field_simp
    · rw [map_div₀, ← coe_psi, ← coe_psi, hx', hy', e, mul_div_cancel_left₀ _ hy0]
  · rintro ⟨a, ⟨x', y', hy', e⟩, rfl⟩
    refine ⟨psi ι x', psi ι y', hy', ?_⟩
    rw [coe_psi, coe_psi, e, map_mul]

end S_exists_valuationSubring_liesOverPrime_forall_mlocal_iff_mem_range
end P2MW
export P2MW.S_exists_valuationSubring_liesOverPrime_forall_mlocal_iff_mem_range (solution)
