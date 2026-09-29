-- Prove2me | solution 1 for groupCohomology.exists_level_sylow_of_primeLocal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/479d7462-ca11-575a-899a-68cb4437ae9d

import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_ExtCitation_LocalLevelSubgroupsPD
import Theorems.Thm_Representation_exists_isGalois_level_forall_apply_eq_self
import Theorems.Thm_groupCohomology_exists_level_ofChar_cycloChar_comp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_exists_level_sylow_of_primeLocal

set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    {p : ℕ} [Fact p.Prime] (q : Nat.Primes)
    (M : Rep (ZMod p) (primeLocalGaloisGroup q)) [FiniteDimensional (ZMod p) M]
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s, primeLocalToGlobal q s ∈ F.fixingSubgroup → M.ρ s m = m) :
    ∃ (U S : Subgroup (primeLocalGaloisGroup q)),
      U ≤ S ∧ U.Normal ∧
      (∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧
        F₀.fixingSubgroup.comap (primeLocalToGlobal q) ≤ U) ∧
      S.FiniteIndex ∧ IsUnit ((S.index : ℕ) : ZMod p) ∧
      (∀ s : primeLocalGaloisGroup q, s ∈ S → ∃ n : ℕ, s ^ (p ^ n) ∈ U) ∧
      (∀ u : primeLocalGaloisGroup q, u ∈ U → ∀ m : M, M.ρ u m = m) ∧
      (∀ u : primeLocalGaloisGroup q, u ∈ U → (cycloChar p) (primeLocalToGlobal q u) = 1) := by
  classical
  have hp : p.Prime := Fact.out

  obtain ⟨FM, hFMfd, hFMgal, hFM⟩ :=
    Representation.exists_isGalois_level_forall_apply_eq_self (primeLocalToGlobal q) M.ρ hsm

  obtain ⟨Fχ, hFχfd, hFχgal, hFχ⟩ :=
    Representation.exists_isGalois_level_forall_apply_eq_self (primeLocalToGlobal q)
      (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))).ρ
      (groupCohomology.exists_level_ofChar_cycloChar_comp (primeLocalToGlobal q))
  haveI := hFMfd; haveI := hFχfd

  haveI hF₀fd : FiniteDimensional ℚ (FM ⊔ Fχ : IntermediateField ℚ (AlgebraicClosure ℚ)) :=
    IntermediateField.finiteDimensional_sup FM Fχ
  haveI hF₀n : Normal ℚ (FM ⊔ Fχ : IntermediateField ℚ (AlgebraicClosure ℚ)) :=
    @IntermediateField.normal_sup ℚ (AlgebraicClosure ℚ) _ _ _ FM Fχ hFMgal.to_normal hFχgal.to_normal
  set U : Subgroup (primeLocalGaloisGroup q) :=
    (FM ⊔ Fχ).fixingSubgroup.comap (primeLocalToGlobal q) with hUdef
  haveI hUn : U.Normal := @ExtCitation.levelSubgroup_normal q (FM ⊔ Fχ) hF₀n
  haveI hUf : U.FiniteIndex := @ExtCitation.levelSubgroup_finiteIndex q (FM ⊔ Fχ) hF₀fd hF₀n
  have hUM : ∀ u : primeLocalGaloisGroup q, u ∈ U → ∀ m : M, M.ρ u m = m := fun u hu m =>
    hFM u (IntermediateField.fixingSubgroup_antitone (le_sup_left : FM ≤ FM ⊔ Fχ) hu) m
  have hUχ : ∀ u : primeLocalGaloisGroup q, u ∈ U → (cycloChar p) (primeLocalToGlobal q u) = 1 := by
    intro u hu
    have h := hFχ u (IntermediateField.fixingSubgroup_antitone (le_sup_right : Fχ ≤ FM ⊔ Fχ) hu) (1 : ZMod p)
    have h' : (((cycloChar p).comp (primeLocalToGlobal q) u : (ZMod p)ˣ) : ZMod p) * 1 = 1 := h
    rw [mul_one, MonoidHom.comp_apply] at h'
    exact Units.val_eq_one.mp h'

  haveI : Finite (primeLocalGaloisGroup q ⧸ U) := Subgroup.finite_quotient_of_finiteIndex
  obtain ⟨P⟩ : Nonempty (Sylow p (primeLocalGaloisGroup q ⧸ U)) := inferInstance
  set S : Subgroup (primeLocalGaloisGroup q) :=
    (P : Subgroup (primeLocalGaloisGroup q ⧸ U)).comap (QuotientGroup.mk' U) with hSdef
  have hUS : U ≤ S := by
    intro u hu
    show QuotientGroup.mk' U u ∈ (P : Subgroup (primeLocalGaloisGroup q ⧸ U))
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff u).mpr hu]
    exact one_mem _
  haveI hSf : S.FiniteIndex := Subgroup.finiteIndex_of_le hUS
  have hidx : S.index = (P : Subgroup (primeLocalGaloisGroup q ⧸ U)).index :=
    Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective U)

  have hndvd : ¬ p ∣ (P : Subgroup (primeLocalGaloisGroup q ⧸ U)).index := P.not_dvd_index
  refine ⟨U, S, hUS, hUn, ⟨FM ⊔ Fχ, hF₀fd, le_rfl⟩, hSf, ?_, ?_, hUM, hUχ⟩
  · rw [hidx, ZMod.isUnit_iff_coprime]
    exact ((Nat.Prime.coprime_iff_not_dvd hp).mpr hndvd).symm
  · intro s hs
    obtain ⟨n, hn⟩ := P.isPGroup' ⟨QuotientGroup.mk' U s, hs⟩
    refine ⟨n, ?_⟩
    have h1 : (QuotientGroup.mk' U s) ^ p ^ n = 1 := by
      have := congrArg Subtype.val hn
      simpa using this
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1

end S_groupCohomology_exists_level_sylow_of_primeLocal
end P2MW
export P2MW.S_groupCohomology_exists_level_sylow_of_primeLocal (solution)
