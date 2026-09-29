-- Prove2me | solution 1 for groupCohomology.exists_corestriction_map_map_res_eq_map_norm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/e4378876-655b-5fe2-ad7f-54e4b57346a4

import Mathlib
import Theorems.Thm_groupCohomology_map_coindFunctor_map_comp_coindIso_hom
import Theorems.Thm_groupCohomology_coindIso_hom_eq_map_subtype_comp_map_eval_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_exists_corestriction_map_map_res_eq_map_norm
set_option autoImplicit false
p2m_open "CategoryTheory groupCohomology P2MW.S_groupCohomology_exists_corestriction_map_map_res_eq_map_norm.groupCohomology"

namespace groupCohomology
p2m_export "groupCohomology" "congr coindIso cochainsMap cochainsMap_comp map_id_comp map map_coindFunctor_map_comp_coindIso_hom coindIso_hom_eq_map_subtype_comp_map_eval_one"
namespace CorNorm
p2m_open "groupCohomology"

section Holes

universe u
variable {k G : Type u} [CommRing k] [Group G] (S : Subgroup G)

theorem coindIso_hom_comp_map {A B : Rep.{u} k S} (ψ : A ⟶ B) (n : ℕ) :
    (coindIso A n).hom ≫ groupCohomology.map (MonoidHom.id S) ψ n =
      groupCohomology.map (MonoidHom.id G) ((Rep.coindFunctor k S.subtype).map ψ) n ≫ (coindIso B n).hom :=
  (groupCohomology.map_coindFunctor_map_comp_coindIso_hom ψ n).symm

theorem map_subtype_id_eq_map_unit_comp_coindIso_hom (R : Rep.{u} k G) (n : ℕ) :
    groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype R)) n =
      groupCohomology.map (MonoidHom.id G) ((Rep.resCoindAdjunction k S.subtype).unit.app R) n ≫
        (coindIso (Rep.res S.subtype R) n).hom := by

  rw [groupCohomology.coindIso_hom_eq_map_subtype_comp_map_eval_one (Rep.res S.subtype R) n
    ((Rep.resCoindAdjunction k S.subtype).counit.app (Rep.res S.subtype R)) (fun _ => rfl)]

  change HomologicalComplex.homologyMap (cochainsMap S.subtype (𝟙 (Rep.res S.subtype R))) n =
    HomologicalComplex.homologyMap (cochainsMap (MonoidHom.id G) ((Rep.resCoindAdjunction k S.subtype).unit.app R)) n ≫
      HomologicalComplex.homologyMap (cochainsMap S.subtype
        (𝟙 (Rep.res S.subtype (Rep.coind S.subtype (Rep.res S.subtype R))))) n ≫
      HomologicalComplex.homologyMap (cochainsMap (MonoidHom.id S)
        ((Rep.resCoindAdjunction k S.subtype).counit.app (Rep.res S.subtype R))) n
  erw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
  congr 1

  have h₁ := cochainsMap_comp S.subtype (MonoidHom.id S)
    (𝟙 (Rep.res S.subtype (Rep.coind S.subtype (Rep.res S.subtype R))))
    ((Rep.resCoindAdjunction k S.subtype).counit.app (Rep.res S.subtype R))
  have h₂ := cochainsMap_comp (MonoidHom.id G) (S.subtype.comp (MonoidHom.id S))
    ((Rep.resCoindAdjunction k S.subtype).unit.app R)
    ((Rep.resFunctor (MonoidHom.id ↥S)).map (𝟙 (Rep.res S.subtype (Rep.coind S.subtype (Rep.res S.subtype R)))) ≫
      (Rep.resCoindAdjunction k S.subtype).counit.app (Rep.res S.subtype R))
  rw [← h₁]
  refine Eq.trans ?_ h₂
  have htri := (Rep.resCoindAdjunction k S.subtype).left_triangle_components R

  have key : (Rep.resFunctor (S.subtype.comp (MonoidHom.id ↥S))).map ((Rep.resCoindAdjunction k S.subtype).unit.app R) ≫
      ((Rep.resFunctor (MonoidHom.id ↥S)).map (𝟙 (Rep.res S.subtype (Rep.coind S.subtype (Rep.res S.subtype R)))) ≫
        (Rep.resCoindAdjunction k S.subtype).counit.app (Rep.res S.subtype R)) =
      (𝟙 (Rep.res S.subtype R) : Rep.res ((MonoidHom.id G).comp (S.subtype.comp (MonoidHom.id ↥S))) R ⟶ _) := by
    rw [← htri]
    rfl
  refine ((congrArg (cochainsMap ((MonoidHom.id G).comp (S.subtype.comp (MonoidHom.id ↥S)))) key).trans ?_).symm
  rfl

end Holes

section Counit

variable {k G : Type} [CommRing k] [Group G] (S : Subgroup G)
  [DecidableRel ⇑(QuotientGroup.rightRel S)] [S.FiniteIndex]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

omit [DecidableRel ⇑(QuotientGroup.rightRel S)] [S.FiniteIndex] in

lemma indRes_counit_mk (C : Rep.{0} k G) (h : G) (b : C) :
    ((Rep.indResAdjunction k S.subtype).counit.app C).hom (Representation.IndV.mk S.subtype (Rep.res S.subtype C).ρ h b) =
      C.ρ h⁻¹ b := by
  simp only [Rep.indResAdjunction, Adjunction.mkOfHomEquiv_counit_app]
  change (Rep.Hom.hom ((Rep.indResHomEquiv S.subtype (Rep.res S.subtype C) C).symm (𝟙 _)))
    (Representation.IndV.mk S.subtype (Rep.res S.subtype C).ρ h b) = C.ρ h⁻¹ b
  rw [Rep.indResHomEquiv_symm_apply]
  simp [Representation.IndV.mk, Representation.Coinvariants.lift_mk, TensorProduct.lift.tmul]

lemma coindRes_counit_apply (C : Rep.{0} k G) (f : Rep.coind S.subtype (Rep.res S.subtype C)) :
    ((Rep.coindResAdjunction k S).counit.app C).hom f =
      ∑ q : Quotient (QuotientGroup.rightRel S), q.liftOn (fun g => C.ρ g⁻¹ (f.1 g)) (by
        rintro g₁ g₂ ⟨s, (hs : (s : G) * g₂ = g₁)⟩
        change C.ρ g₁⁻¹ (f.1 g₁) = C.ρ g₂⁻¹ (f.1 g₂)
        have hf : f.1 ((s : G) * g₂) = C.ρ (s : G) (f.1 g₂) := f.2 s g₂
        rw [← hs, hf, mul_inv_rev, map_mul, Module.End.mul_apply, ← Module.End.mul_apply (C.ρ (↑s)⁻¹), ← map_mul,
          inv_mul_cancel, map_one, Module.End.one_apply]) := by
  rw [Rep.coindResAdjunction_counit_app]
  change ((Rep.indResAdjunction k S.subtype).counit.app C).hom (((Rep.res S.subtype C).indCoindIso.inv).hom f) = _
  have hinv : ((Rep.res S.subtype C).indCoindIso.inv).hom f = (Rep.res S.subtype C).coindToInd f := rfl
  rw [hinv, Rep.coindToInd_apply]
  rw [show ∀ y, (Rep.Hom.hom ((Rep.indResAdjunction k S.subtype).counit.app C)) y =
      (Rep.Hom.hom ((Rep.indResAdjunction k S.subtype).counit.app C)).toLinearMap y from fun _ => rfl]
  erw [map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  induction q using Quotient.inductionOn with
  | h g => exact indRes_counit_mk S C g (f.1 g)

omit [DecidableRel ⇑(QuotientGroup.rightRel S)] [S.FiniteIndex] in

lemma coindMap_unit_apply (R C : Rep.{0} k G) (φ : Rep.res S.subtype R ⟶ Rep.res S.subtype C) (x : R) (g : G) :
    (((Rep.resCoindAdjunction k S.subtype).unit.app R ≫ (Rep.coindFunctor k S.subtype).map φ).hom x).1 g =
      φ.hom (R.ρ g x) := rfl

theorem unit_coindMap_counit_eq [Fintype (G ⧸ S)] (R C : Rep.{0} k G) (φ : Rep.res S.subtype R ⟶ Rep.res S.subtype C)
    (Nφ : R ⟶ C) (hN : ∀ x : R, Nφ.hom x = ∑ g : G ⧸ S, C.ρ g.out (φ.hom (R.ρ g.out⁻¹ x))) :
    (Rep.resCoindAdjunction k S.subtype).unit.app R ≫ (Rep.coindFunctor k S.subtype).map φ ≫
      (Rep.coindResAdjunction k S).counit.app C = Nφ := by

  obtain rfl : ‹Fintype (G ⧸ S)› = Subgroup.fintypeQuotientOfFiniteIndex := Subsingleton.elim _ _
  refine Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun x => ?_))
  change _ = Nφ.hom x
  rw [hN x]
  change ((Rep.coindResAdjunction k S).counit.app C).hom
    ((((Rep.resCoindAdjunction k S.subtype).unit.app R ≫ (Rep.coindFunctor k S.subtype).map φ).hom x)) = _
  rw [coindRes_counit_apply]
  apply Fintype.sum_equiv (QuotientGroup.quotientRightRelEquivQuotientLeftRel S)
  intro q
  induction q using Quotient.inductionOn with
  | h g =>
  change C.ρ g⁻¹ ((((Rep.resCoindAdjunction k S.subtype).unit.app R ≫ (Rep.coindFunctor k S.subtype).map φ).hom x).1 g) = _
  rw [coindMap_unit_apply]

  set a : G := ((QuotientGroup.quotientRightRelEquivQuotientLeftRel S) (Quotient.mk _ g)).out with ha_def
  have ha : (QuotientGroup.mk a : G ⧸ S) = QuotientGroup.mk g⁻¹ :=
    Quotient.out_eq ((QuotientGroup.quotientRightRelEquivQuotientLeftRel S) (Quotient.mk _ g))
  rw [QuotientGroup.eq] at ha

  set s : S := ⟨a⁻¹ * g⁻¹, ha⟩ with hs_def
  have ha1 : a⁻¹ = (s : G) * g := by rw [hs_def]; group
  have ha2 : a = g⁻¹ * (s : G)⁻¹ := by rw [← inv_inj, ha1, mul_inv_rev, inv_inv, inv_inv]
  rw [ha1, ha2, map_mul, Module.End.mul_apply]
  have hφ : φ.hom (R.ρ ((s : G) * g) x) = C.ρ (s : G) (φ.hom (R.ρ g x)) := by
    rw [map_mul, Module.End.mul_apply]
    exact Rep.hom_comm_apply φ s (R.ρ g x)
  rw [hφ, ← Module.End.mul_apply (C.ρ (↑s)⁻¹), ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

end Counit

end groupCohomology.CorNorm

namespace groupCohomology p2m_export "groupCohomology" "congr coindIso cochainsMap cochainsMap_comp map_id_comp map map_coindFunctor_map_comp_coindIso_hom coindIso_hom_eq_map_subtype_comp_map_eval_one" namespace CorNorm end groupCohomology.CorNorm
p2m_open_scoped "groupCohomology" in

theorem groupCohomology.CorNorm.cor_formula
    {k G : Type} [CommRing k] [Group G] (S : Subgroup G)
    [DecidableRel ⇑(QuotientGroup.rightRel S)] [S.FiniteIndex] [Fintype (G ⧸ S)]
    (R C : Rep k G) (φ : Rep.res S.subtype R ⟶ Rep.res S.subtype C)
    (Nφ : R ⟶ C)
    (hN : ∀ x : R, Nφ.hom x = ∑ g : G ⧸ S, C.ρ g.out (φ.hom (R.ρ g.out⁻¹ x)))
    (n : ℕ) (z : groupCohomology R n) :
    (groupCohomology.map (MonoidHom.id G) ((Rep.coindResAdjunction k S).counit.app C) n).hom
        ((groupCohomology.coindIso (Rep.res S.subtype C) n).inv
          ((groupCohomology.map (MonoidHom.id ↥S) φ n).hom
            ((groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype R)) n).hom z)))
      = (groupCohomology.map (MonoidHom.id G) Nφ n).hom z := by
  have hcomp : (Rep.resCoindAdjunction k S.subtype).unit.app R ≫ (Rep.coindFunctor k S.subtype).map φ ≫
      (Rep.coindResAdjunction k S).counit.app C = Nφ :=
    groupCohomology.CorNorm.unit_coindMap_counit_eq S R C φ Nφ hN
  have key : groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype R)) n ≫ groupCohomology.map (MonoidHom.id ↥S) φ n ≫
      (groupCohomology.coindIso (Rep.res S.subtype C) n).inv ≫
      groupCohomology.map (MonoidHom.id G) ((Rep.coindResAdjunction k S).counit.app C) n =
      groupCohomology.map (MonoidHom.id G) Nφ n := by
    rw [groupCohomology.CorNorm.map_subtype_id_eq_map_unit_comp_coindIso_hom S R n, Category.assoc]
    erw [reassoc_of% (groupCohomology.CorNorm.coindIso_hom_comp_map S φ n), Iso.hom_inv_id_assoc]
    erw [← groupCohomology.map_id_comp, ← groupCohomology.map_id_comp, hcomp]
  have hz := congrArg (fun F => F.hom z) key
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hz
  exact hz

open CategoryTheory _root_.groupCohomology _root_.P2MW.S_groupCohomology_exists_corestriction_map_map_res_eq_map_norm.groupCohomology in

theorem solution
    {k G : Type} [CommRing k] [Group G] (S : Subgroup G) [S.FiniteIndex] [Fintype (G ⧸ S)]
    (C : Rep k G) (n : ℕ) :
    ∃ cor : groupCohomology (Rep.res S.subtype C) n →+ groupCohomology C n,
      ∀ (R : Rep k G) (φ : Rep.res S.subtype R ⟶ Rep.res S.subtype C)
        (Nφ : R ⟶ C)
        (_ : ∀ x : R, Nφ.hom x = ∑ g : G ⧸ S, C.ρ g.out (φ.hom (R.ρ g.out⁻¹ x)))
        (z : groupCohomology R n),
        cor ((groupCohomology.map (MonoidHom.id ↥S) φ n).hom
              ((groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype R)) n).hom z))
          = (groupCohomology.map (MonoidHom.id G) Nφ n).hom z := by
  classical
  refine ⟨(((groupCohomology.coindIso (Rep.res S.subtype C) n).inv ≫
      groupCohomology.map (MonoidHom.id G) ((Rep.coindResAdjunction k S).counit.app C) n).hom).toAddMonoidHom,
    fun R φ Nφ hN z => ?_⟩
  exact groupCohomology.CorNorm.cor_formula S R C φ Nφ hN n z

end S_groupCohomology_exists_corestriction_map_map_res_eq_map_norm
end P2MW
export P2MW.S_groupCohomology_exists_corestriction_map_map_res_eq_map_norm (solution)
