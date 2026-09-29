-- Prove2me | solution 1 for groupCohomology.nonempty_continuousHSr_linearEquiv_of_iso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/41f918da-8a47-5467-95f8-72692bf7d66c

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_nonempty_continuousHSr_linearEquiv_of_iso

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module groupCohomology ExtCitation"
open scoped Classical

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 1600000
set_option Elab.async false

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module groupCohomology ExtCitation"
open scoped Classical

namespace HsrIso

section
variable {k : Type} [CommRing k] {G : Type} [Group G]
  (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (S : Finset Nat.Primes)

noncomputable abbrev H1F {A B : Rep.{0} k G} (φ : A ⟶ B) :
    ↥(continuousH1Sr r S A) →ₗ[k] ↥(continuousH1Sr r S B) :=
  continuousH1SrMap (rH := r) (rG := r) (MonoidHom.id G) (fun _ => rfl) S
    (show Rep.res (MonoidHom.id G) A ⟶ B from φ)

lemma H1F_comp {A B C : Rep.{0} k G} (φ : A ⟶ B) (ψ : B ⟶ C) :
    H1F r S (φ ≫ ψ) = H1F r S ψ ∘ₗ H1F r S φ := by
  apply LinearMap.ext; intro x; apply Subtype.ext
  show (groupCohomology.map (MonoidHom.id G) (φ ≫ ψ) 1).hom (x : H1 A) =
    (groupCohomology.map (MonoidHom.id G) ψ 1).hom
      ((groupCohomology.map (MonoidHom.id G) φ 1).hom (x : H1 A))
  rw [groupCohomology.map_id_comp]
  rfl

lemma H1F_id (A : Rep.{0} k G) : H1F r S (𝟙 A) = LinearMap.id := by
  apply LinearMap.ext; intro x; apply Subtype.ext
  show (groupCohomology.map (MonoidHom.id G) (𝟙 A) 1).hom (x : H1 A) = (x : H1 A)
  rw [groupCohomology.map_id]
  rfl

variable {A B : Rep.{0} k G} (e : A ≅ B)

noncomputable def H1SrEquiv : ↥(continuousH1Sr r S A) ≃ₗ[k] ↥(continuousH1Sr r S B) :=
  LinearEquiv.ofLinear (H1F r S e.hom) (H1F r S e.inv)
    (by rw [← H1F_comp, e.inv_hom_id, H1F_id])
    (by rw [← H1F_comp, e.hom_inv_id, H1F_id])

noncomputable def H2SrEquiv : continuousH2Sr r S A ≃ₗ[k] continuousH2Sr r S B :=
  LinearEquiv.ofLinear (continuousH2SrMapHom S r e.hom) (continuousH2SrMapHom S r e.inv)
    (by rw [← continuousH2SrMapHom_comp, e.inv_hom_id, continuousH2SrMapHom_id])
    (by rw [← continuousH2SrMapHom_comp, e.hom_inv_id, continuousH2SrMapHom_id])

end

end HsrIso
theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    {A B : Rep.{0} (ZMod p) ↥K.fixingSubgroup} (e : A ≅ B) :
    Nonempty (↥(continuousH1Sr K.fixingSubgroup.subtype S A) ≃ₗ[ZMod p] ↥(continuousH1Sr K.fixingSubgroup.subtype S B)) ∧
      Nonempty (continuousH2Sr K.fixingSubgroup.subtype S A ≃ₗ[ZMod p] continuousH2Sr K.fixingSubgroup.subtype S B) :=
  ⟨⟨HsrIso.H1SrEquiv K.fixingSubgroup.subtype S e⟩, ⟨HsrIso.H2SrEquiv K.fixingSubgroup.subtype S e⟩⟩

end S_groupCohomology_nonempty_continuousHSr_linearEquiv_of_iso
end P2MW
export P2MW.S_groupCohomology_nonempty_continuousHSr_linearEquiv_of_iso (solution)
