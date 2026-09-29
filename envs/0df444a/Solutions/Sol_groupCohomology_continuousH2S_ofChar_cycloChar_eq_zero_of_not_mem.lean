-- Prove2me | solution 1 for groupCohomology.continuousH2S_ofChar_cycloChar_eq_zero_of_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/d35f60f5-3171-527d-a10e-f5c50c02808d

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_FieldTheory_RatAlgClosureGalois
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ValuationSubring_exists_liesOverPrime_algebraicClosure_rat
import Theorems.Thm_IntermediateField_IsUnramifiedOutside_normalClosure
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_cycloChar_ne_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_continuousH2S_ofChar_cycloChar_eq_zero_of_not_mem

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
p2m_open "CategoryTheory Module groupCohomology P2MW.S_groupCohomology_continuousH2S_ofChar_cycloChar_eq_zero_of_not_mem.groupCohomology ExtCitation"

namespace groupCohomology
p2m_export "groupCohomology" "cocycles₂ mem_cocycles₂_iff mem_levelCochainsS₂_iff continuousH2S ofChar"
namespace C7aBody
p2m_open "groupCohomology"

variable {p : ℕ} [Fact p.Prime]

private theorem apply_eq_pow_cycloChar (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (μ : AlgebraicClosure ℚ)
    (hμ : μ ^ p = 1) : σ μ = μ ^ ((cycloChar p σ : ZMod p)).val := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [zero_pow (Fact.out : p.Prime).ne_zero] at hμ
    exact zero_ne_one hμ
  set t : (AlgebraicClosure ℚ)ˣ := Units.mk0 μ hμ0 with ht
  have htmem : t ∈ rootsOfUnity p (AlgebraicClosure ℚ) := by
    rw [mem_rootsOfUnity]
    ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, hμ, Units.val_one]
  have h := modularCyclotomicCharacter.spec (AlgebraicClosure ℚ) (n := p) (card_rootsOfUnity_eq_self p) σ.toRingEquiv htmem
  rw [Units.val_mk0] at h
  exact h

private theorem eq_zero_of_const_of_cycloChar_ne_one
    (f : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →
      (ofChar (k := ZMod p) (cycloChar p)))
    (hf : f ∈ cocycles₂ (ofChar (k := ZMod p) (cycloChar p)))
    (N : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hN : ∀ (h : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      s ∈ N → h⁻¹ * s * h ∈ N)
    (hconst : ∀ g g' s s', s ∈ N → s' ∈ N → f (g * s, g' * s') = f (g, g'))
    (s₀ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hs₀ : s₀ ∈ N) (hχ : cycloChar p s₀ ≠ 1) :
    f = 0 := by
  have hc := (mem_cocycles₂_iff f).1 hf
  have one_mem : (1 : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ N := by
    simpa using hN s₀ s₀ hs₀

  have c1 : ∀ g j s, s ∈ N → f (g * s, j) = f (g, j) := fun g j s hs => by
    simpa using hconst g j s 1 hs one_mem
  have c2 : ∀ g j s, s ∈ N → f (g, j * s) = f (g, j) := fun g j s hs => by
    simpa using hconst g j 1 s one_mem hs

  have l1 : ∀ h j s, s ∈ N → f (s * h, j) = f (h, j) := fun h j s hs => by
    have : s * h = h * (h⁻¹ * s * h) := by group
    rw [this, c1 h j _ (hN h s hs)]
  have l2 : ∀ g j s, s ∈ N → f (g, s * j) = f (g, j) := fun g j s hs => by
    have : s * j = j * (j⁻¹ * s * j) := by group
    rw [this, c2 g j _ (hN j s hs)]

  have hA : ∀ g j, f (g, 1) = (ofChar (k := ZMod p) (cycloChar p)).ρ g (f (1, j)) := fun g j => by
    have h := hc g s₀ j
    rw [c1 g j s₀ hs₀, l2 g j s₀ hs₀] at h

    have e1 : f (g, s₀) = f (g, 1) := by simpa using c2 g 1 s₀ hs₀
    have e2 : f (s₀, j) = f (1, j) := by simpa using l1 1 j s₀ hs₀
    rw [e1, e2] at h
    exact (add_left_cancel (h.trans (add_comm _ _)))
  have hB : ∀ j, f (1, j) = f (1, 1) := fun j => by
    have h := hA 1 j
    rw [map_one] at h
    exact h.symm

  funext gj
  obtain ⟨h, j⟩ := gj
  have hh := hc s₀ h j
  have e1 : f (s₀ * h, j) = f (h, j) := l1 h j s₀ hs₀
  have e2 : f (s₀, h) = f (1, 1) := by
    have : f (s₀, h) = f (1, h) := by simpa using l1 1 h s₀ hs₀
    exact this.trans (hB h)
  have e3 : f (s₀, h * j) = f (1, 1) := by
    have : f (s₀, h * j) = f (1, h * j) := by simpa using l1 1 (h * j) s₀ hs₀
    exact this.trans (hB (h * j))
  rw [e1, e2, e3] at hh

  have hh' : f (h, j) = (cycloChar p s₀ : ZMod p) * f (h, j) := add_right_cancel hh
  show f (h, j) = 0
  have hunit : ((cycloChar p s₀ : ZMod p) - 1) ≠ 0 := by
    intro h0
    apply hχ
    ext
    rw [Units.val_one]
    exact (sub_eq_zero.1 h0)
  have : ((cycloChar p s₀ : ZMod p) - 1) * f (h, j) = 0 := by
    rw [sub_mul, one_mul, ← hh', sub_self]
  simpa [hunit] using this

end groupCohomology.C7aBody

open groupCohomology.C7aBody in
theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hp2 : p ≠ 2) (hpS : pPrime p ∉ S)
    (c : continuousH2S S (ofChar (k := ZMod p) (cycloChar p))) : c = 0 := by
  classical
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  suffices hf0 : (f : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →
      (ofChar (k := ZMod p) (cycloChar p))) = 0 by
    have : f = 0 := Subtype.ext hf0
    rw [this]; rfl
  obtain ⟨hcoc, hlev⟩ := f.2
  obtain ⟨F, hF, hconstF⟩ := (mem_levelCochainsS₂_iff S _ _).1 hlev

  set F' := IntermediateField.normalClosure ℚ F (AlgebraicClosure ℚ) with hF'def
  have hF' : F'.IsUnramifiedOutside S := hF.normalClosure
  haveI := hF.1
  haveI : IsGalois ℚ ↥F' := IsGalois.normalClosure ℚ ↥F (AlgebraicClosure ℚ)
  have hle : F ≤ F' := IntermediateField.le_normalClosure F
  have hsub : F'.fixingSubgroup ≤ F.fixingSubgroup := IntermediateField.fixingSubgroup_antitone hle

  have hN : ∀ (h s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), s ∈ F'.fixingSubgroup → h⁻¹ * s * h ∈ F'.fixingSubgroup := by
    intro h s hs
    rw [IntermediateField.mem_fixingSubgroup_iff] at hs ⊢
    intro x hx
    have hx' : h x ∈ F' := (IntermediateField.normal_iff_forall_map_le'.1 inferInstance h) ⟨x, hx, rfl⟩
    show h⁻¹ (s (h x)) = x
    rw [hs _ hx', ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]

  obtain ⟨A, hA⟩ := ValuationSubring.exists_liesOverPrime_algebraicClosure_rat (pPrime p)
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hid : (MonoidHom.id (ZMod p)ˣ) ≠ 1 := by
    intro h
    have h2 : ((-1 : (ZMod p)ˣ) : (ZMod p)ˣ) = 1 := by simpa using DFunLike.congr_fun h (-1)
    have h3 : ((-1 : ZMod p)) = 1 := by simpa using congrArg Units.val h2
    have h4 : ((2 : ℕ) : ZMod p) = 0 := by
      have : (1 : ZMod p) + 1 = 0 := by
        nth_rewrite 1 [← h3]
        exact neg_add_cancel 1
      exact_mod_cast this
    rw [ZMod.natCast_eq_zero_iff] at h4
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).1 h4)
  obtain ⟨s₀, hs₀I, hχ⟩ := ValuationSubring.exists_mem_inertiaSubgroupIn_cycloChar_ne_one p Fact.out p
    (Or.inl ⟨hodd, rfl⟩) (cycloChar p) (fun σ μ hμ => apply_eq_pow_cycloChar σ μ hμ) (MonoidHom.id (ZMod p)ˣ) hid A hA
  have hs₀ : s₀ ∈ F'.fixingSubgroup := hF'.2 (pPrime p) hpS A hA hs₀I
  exact eq_zero_of_const_of_cycloChar_ne_one (p := p) f hcoc F'.fixingSubgroup hN
    (fun g g' s s' hs hs' => hconstF g g' s s' (hsub hs) (hsub hs')) s₀ hs₀ (by simpa using hχ)

end S_groupCohomology_continuousH2S_ofChar_cycloChar_eq_zero_of_not_mem
end P2MW
export P2MW.S_groupCohomology_continuousH2S_ofChar_cycloChar_eq_zero_of_not_mem (solution)
