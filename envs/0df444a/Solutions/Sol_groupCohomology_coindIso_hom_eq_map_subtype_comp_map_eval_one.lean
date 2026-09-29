-- Prove2me | solution 1 for groupCohomology.coindIso_hom_eq_map_subtype_comp_map_eval_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/f61c5e9d-330f-5e81-90da-518a574d2b22

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_coindIso_hom_eq_map_subtype_comp_map_eval_one

set_option autoImplicit false

open CategoryTheory Opposite

namespace ShapiroRes

universe w v u' u

section General

variable {R : Type w} [Ring R] {C : Type u'} [Category.{v} C] [Abelian C] [Linear R C]

noncomputable def precompGen {X : C} (P Q : ProjectiveResolution X) (φ : P.complex ⟶ Q.complex) (Y : C) :
    Q.complex.linearYonedaObj R Y ⟶ P.complex.linearYonedaObj R Y :=
  (HomologicalComplex.unopFunctor (ModuleCat R) (ComplexShape.down ℕ)).map
    ((((linearYoneda R C).obj Y).rightOp.mapHomologicalComplex (ComplexShape.down ℕ)).map φ).op

theorem precompGen_f {X : C} (P Q : ProjectiveResolution X) (φ : P.complex ⟶ Q.complex) (Y : C) (i : ℕ) :
    (precompGen (R := R) P Q φ Y).f i = ((linearYoneda R C).obj Y).map (φ.f i).op := rfl

theorem precompGen_f_apply {X : C} (P Q : ProjectiveResolution X) (φ : P.complex ⟶ Q.complex) (Y : C) (i : ℕ)
    (g : Q.complex.X i ⟶ Y) :
    ((precompGen (R := R) P Q φ Y).f i).hom g = φ.f i ≫ g := rfl

variable [EnoughProjectives C]

set_option maxHeartbeats 3200000 in

theorem isoExt_inv_comp_isoExt_hom_gen {X : C} (P Q : ProjectiveResolution X) (φ : P.complex ⟶ Q.complex)
    (hφ : φ.f 0 ≫ Q.π.f 0 = P.π.f 0) (Y : C) (n : ℕ) :
    (Q.isoExt (R := R) n Y).inv ≫ (P.isoExt n Y).hom = HomologicalComplex.homologyMap (precompGen P Q φ Y) n := by
  have hnat := ProjectiveResolution.isoLeftDerivedObj_inv_naturality (𝟙 X) P Q φ
    (by erw [Category.comp_id]; exact hφ) ((linearYoneda R C).obj Y).rightOp n
  rw [CategoryTheory.Functor.map_id, Category.comp_id] at hnat
  have h2 : (P.isoLeftDerivedObj ((linearYoneda R C).obj Y).rightOp n).inv ≫
      (Q.isoLeftDerivedObj ((linearYoneda R C).obj Y).rightOp n).hom =
      HomologicalComplex.homologyMap
        ((((linearYoneda R C).obj Y).rightOp.mapHomologicalComplex (ComplexShape.down ℕ)).map φ) n := by
    rw [hnat]
    erw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rfl
  have h3 := HomologicalComplex.homologyOp_hom_naturality (precompGen (R := R) P Q φ Y) n
  dsimp only [ProjectiveResolution.isoExt, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Iso.unop_hom, Iso.unop_inv]
  erw [Category.assoc, ← Category.assoc (Q.isoLeftDerivedObj ((linearYoneda R C).obj Y).rightOp n).hom.unop,
    ← unop_comp, h2]
  apply Quiver.Hom.op_inj
  simp only [op_comp, Quiver.Hom.op_unop, Category.assoc]
  exact (Iso.inv_comp_eq _).mpr h3

end General

section Bar

variable {k G : Type u} [CommRing k] [Group G] {S : Subgroup G}

noncomputable abbrev resBar (k G : Type u) [CommRing k] [Group G] (S : Subgroup G) :
    ProjectiveResolution (Rep.trivial k S k) :=
  (Rep.resFunctor S.subtype).mapProjectiveResolution (Rep.barResolution k G)

noncomputable def precomp (A : Rep.{u} k S) {P Q : ChainComplex (Rep.{u} k S) ℕ} (φ : P ⟶ Q) :
    Q.linearYonedaObj k A ⟶ P.linearYonedaObj k A where
  f i := ModuleCat.ofHom (Linear.leftComp k A (φ.f i))
  comm' i j hij := by
    ext g
    show P.d j i ≫ (φ.f i ≫ g) = φ.f j ≫ (Q.d j i ≫ g)
    rw [← Category.assoc, ← Category.assoc, φ.comm]

theorem precomp_f_apply (A : Rep.{u} k S) {P Q : ChainComplex (Rep.{u} k S) ℕ} (φ : P ⟶ Q) (i : ℕ) (g : Q.X i ⟶ A) :
    (precomp A φ).f i g = φ.f i ≫ g := rfl

theorem precomp_eq_precompGen (A : Rep.{u} k S)
    (φ : (Rep.barResolution k S).complex ⟶ (resBar k G S).complex) :
    precomp A φ = precompGen (Rep.barResolution k S) (resBar k G S) φ A := by
  ext i g
  rfl

theorem isoExt_inv_comp_isoExt_hom (A : Rep.{u} k S) (n : ℕ)
    (φ : (Rep.barResolution k S).complex ⟶ (resBar k G S).complex)
    (hφ : φ ≫ (resBar k G S).π = (Rep.barResolution k S).π) :
    ((resBar k G S).isoExt n A).inv ≫ ((Rep.barResolution k S).isoExt n A).hom =
      HomologicalComplex.homologyMap (precomp A φ) n := by
  rw [precomp_eq_precompGen]
  refine isoExt_inv_comp_isoExt_hom_gen _ _ φ ?_ A n
  rw [← HomologicalComplex.comp_f, hφ]

section Diag0
open Finsupp
open scoped _root_.CategoryTheory.MonoidalCategory in
set_option backward.isDefEq.respectTransparency false in
theorem diagonalSuccIsoFree_inv_hom_single_single (n : ℕ) (f : Fin n → G) (g : G) (r : k) :
    (Rep.diagonalSuccIsoFree k G n).inv.hom (single f (MonoidAlgebra.single g r)) =
      MonoidAlgebra.single (g • Fin.partialProd f) r := by
  simp only [Rep.diagonalSuccIsoFree, Rep.diagonalSuccIsoTensorTrivial, Iso.trans_inv, Rep.hom_comp,
    Representation.IntertwiningMap.comp_apply]
  have step1 : (Rep.Hom.hom (Rep.leftRegularTensorTrivialIsoFree k G (Fin n → G)).inv)
      (single f (.single g r)) = .single g 1 ⊗ₜ[k] .single f r :=
    Representation.leftRegularTensorTrivialIsoFree_symm_apply_single_single f g r
  rw [step1]
  simp only [Rep.mkIso_inv, Representation.linearizeOfMulActionIso, Representation.Equiv.mk_symm,
    LinearEquiv.refl_symm, ConcreteCategory.hom_ofHom, Action.tensorObj_V, Action.trivial_V,
    Functor.mapIso_inv, Rep.tensor_V, Rep.tensor_ρ, Iso.symm_inv, Functor.Monoidal.μIso_hom, Rep.μ_hom,
    MonoidalCategory.tensorIso_inv, Representation.linearizeTrivialIso, Rep.hom_tensorHom,
    Representation.IntertwiningMap.tensor_apply, Representation.Equiv.coe_toIntertwiningMap,
    Representation.Equiv.mk_apply, LinearEquiv.refl_apply]
  have key₁ := Representation.linearizeMap_single (k := k)
    (Action.diagonalSuccIsoTensorTrivial G n).inv (g, f) ((1 : k) * r)
  have key₂ := Representation.LinearizeMonoidal.μ_apply_single_single (k := k)
    (X := Action.leftRegular G) (Y := Action.trivial G (Fin n → G)) g f 1 r
  exact ((congrArg (fun z => (Representation.linearizeMap
    (Action.diagonalSuccIsoTensorTrivial G n).inv) z) key₂).trans key₁).trans
    (by rw [one_mul]; exact congrArg (MonoidAlgebra.single · r) (Action.diagonalSuccIsoTensorTrivial_inv_hom_apply g f))

set_option backward.isDefEq.respectTransparency false in

theorem diagonalSuccIsoFree_zero_inv_hom_single_single (y : Fin 0 → G) (g : G) (r : k) :
    (Rep.diagonalSuccIsoFree k G 0).inv.hom (single y (MonoidAlgebra.single g r)) =
      MonoidAlgebra.single (fun _ => g) r := by
  rw [diagonalSuccIsoFree_inv_hom_single_single]
  congr 1
  funext i
  simp [Fin.partialProd]

theorem standardComplex_ε_hom_single (x : Fin 1 → G) (r : k) :
    (Rep.standardComplex.ε k G).hom (MonoidAlgebra.single x r) = r := by
  simp [Rep.standardComplex.ε]

end Diag0

noncomputable def barInclusionF (k G : Type u) [CommRing k] [Group G] (S : Subgroup G) (n : ℕ) :
    Rep.free k S (Fin n → S) ⟶ Rep.res S.subtype (Rep.free k G (Fin n → G)) :=
  Rep.freeLift k S (Rep.res S.subtype (Rep.free k G (Fin n → G)))
    (fun y => Finsupp.single (S.subtype ∘ y) (MonoidAlgebra.single 1 1))

theorem barInclusionF_single_single (n : ℕ) (y : Fin n → S) (s : S) (r : k) :
    (barInclusionF k G S n).hom (Finsupp.single y (MonoidAlgebra.single s r)) =
      Finsupp.single (S.subtype ∘ y) (MonoidAlgebra.single (s : G) r) := by
  rw [barInclusionF, Rep.hom_ofHom, Representation.freeLift_single_single]
  simp

theorem barInclusionF_comm (n : ℕ) :
    barInclusionF k G S (n + 1) ≫ (Rep.resFunctor S.subtype).map (Rep.barComplex.d k G n) =
      Rep.barComplex.d k S n ≫ barInclusionF k G S n := by
  refine Rep.free_ext k S _ _ _ fun x => ?_
  simp only [Rep.hom_comp]
  show (Rep.barComplex.d k G n).hom ((barInclusionF k G S (n + 1)).hom (Finsupp.single x (MonoidAlgebra.single 1 1))) =
    (barInclusionF k G S n).hom ((Rep.barComplex.d k S n).hom (Finsupp.single x (MonoidAlgebra.single 1 1)))
  rw [barInclusionF_single_single, OneMemClass.coe_one, Rep.barComplex.d_single, Rep.barComplex.d_single, map_add,
    map_sum, barInclusionF_single_single]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [barInclusionF_single_single, OneMemClass.coe_one, Fin.comp_contractNth]
  intro a b
  exact Subgroup.coe_mul S a b

noncomputable def barInclusion (k G : Type u) [CommRing k] [Group G] (S : Subgroup G) :
    (Rep.barResolution k S).complex ⟶ (resBar k G S).complex where
  f n := barInclusionF k G S n
  comm' i j hij := by
    obtain rfl : j + 1 = i := hij
    show barInclusionF k G S (j + 1) ≫ (Rep.resFunctor S.subtype).map ((Rep.barComplex k G).d (j + 1) j) =
      (Rep.barComplex k S).d (j + 1) j ≫ barInclusionF k G S j
    rw [Rep.barComplex.d_def, Rep.barComplex.d_def]
    exact barInclusionF_comm (k := k) (G := G) (S := S) j

omit [Group G] in
theorem freeLiftLEquiv_apply' {H : Type u} [Group H] {α : Type u} (X : Rep.{u} k H) (c : Rep.free k H α ⟶ X) (i : α) :
    Rep.freeLiftLEquiv k H α X c i = c.hom (Finsupp.single i (MonoidAlgebra.single 1 1)) := rfl

omit [Group G] in
theorem freeLiftLEquiv_symm_hom {H : Type u} [Group H] {α : Type u} (X : Rep.{u} k H) (F : α → X) :
    ((Rep.freeLiftLEquiv k H α X).symm F).hom = Representation.freeLift X.ρ F := rfl

theorem barInclusion_f (n : ℕ) : (barInclusion k G S).f n = barInclusionF k G S n := rfl

theorem resCoindHomEquiv_symm_hom_apply {B : Rep.{u} k G} (A : Rep.{u} k S) (a : B ⟶ Rep.coind S.subtype A) (v : B) :
    ((Rep.resCoindHomEquiv.{u} S.subtype B A).symm a).hom v = ((a.hom v : Rep.coind S.subtype A) : G → A) 1 := rfl

theorem cochain_identity (A : Rep.{u} k S) (ev : Rep.res S.subtype (Rep.coind S.subtype A) ⟶ A)
    (hev : ∀ f : Rep.res S.subtype (Rep.coind S.subtype A), ev.hom f = (f : G → A) 1) :
    (groupCohomology.inhomogeneousCochainsIso (Rep.coind S.subtype A)).hom ≫
        (groupCohomology.linearYonedaObjResProjectiveResolutionIso (Rep.barResolution k G) A).inv ≫
          precomp A (barInclusion k G S) ≫ (groupCohomology.inhomogeneousCochainsIso A).inv =
      groupCohomology.cochainsMap S.subtype ev := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  refine ModuleCat.hom_ext (LinearMap.ext fun f => funext fun y => ?_)

  rw [groupCohomology.cochainsMap_f]
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.funLeft_apply, LinearMap.compLeft_apply]

  simp only [groupCohomology.inhomogeneousCochainsIso, groupCohomology.linearYonedaObjResProjectiveResolutionIso,
    HomologicalComplex.Hom.isoOfComponents_hom_f, HomologicalComplex.Hom.isoOfComponents_inv_f, Iso.symm_hom, Iso.symm_inv,
    LinearEquiv.toModuleIso_hom, LinearEquiv.toModuleIso_inv, precomp_f_apply]
  show (Rep.freeLiftLEquiv k S (Fin n → S) A) ((barInclusion k G S).f n ≫
      (Rep.resCoindHomEquiv S.subtype _ A).symm ((Rep.freeLiftLEquiv k G (Fin n → G) (Rep.coind S.subtype A)).symm f)) y =
    ev.hom (f (S.subtype ∘ y))
  rw [hev, freeLiftLEquiv_apply', Rep.hom_comp, Representation.IntertwiningMap.comp_apply, barInclusion_f]
  erw [barInclusionF_single_single (k := k) (G := G) (S := S) n y 1 1]
  rw [OneMemClass.coe_one]
  erw [resCoindHomEquiv_symm_hom_apply, freeLiftLEquiv_symm_hom (k := k) (Rep.coind S.subtype A) f,
    Representation.freeLift_single_single]
  rw [one_smul, map_one, Module.End.one_apply]

theorem barResolution_π_f_zero_hom_single_single {H : Type u} [Group H] (x : Fin 0 → H) (g : H) (r : k) :
    ((Rep.barResolution k H).π.f 0).hom (Finsupp.single x (MonoidAlgebra.single g r)) = (r : k) := by
  unfold Rep.barResolution
  dsimp only
  rw [HomologicalComplex.comp_f]
  erw [Rep.hom_comp, Representation.IntertwiningMap.comp_apply]
  simp only [Rep.barComplex.isoStandardComplex, HomologicalComplex.Hom.isoOfComponents_hom_f, Iso.symm_hom]
  erw [diagonalSuccIsoFree_zero_inv_hom_single_single]
  rw [Rep.standardComplex.εToSingle₀]
  erw [ChainComplex.toSingle₀Equiv_symm_apply_f_zero]
  exact standardComplex_ε_hom_single _ _

theorem barInclusion_comp_π (k G : Type u) [CommRing k] [Group G] (S : Subgroup G) :
    barInclusion k G S ≫ (resBar k G S).π = (Rep.barResolution k S).π := by
  refine HomologicalComplex.to_single_hom_ext ?_
  rw [HomologicalComplex.comp_f, Functor.mapProjectiveResolution_π, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplex_map_f, HomologicalComplex.singleMapHomologicalComplex_hom_app_self]
  refine Rep.free_ext k S _ _ _ fun y => ?_
  rw [barInclusion_f]
  erw [Rep.hom_comp, Rep.hom_comp, Rep.hom_comp, Representation.IntertwiningMap.comp_apply,
    Representation.IntertwiningMap.comp_apply, Representation.IntertwiningMap.comp_apply]
  erw [barInclusionF_single_single (k := k) (G := G) (S := S) 0 y 1 1]
  rw [OneMemClass.coe_one]
  erw [barResolution_π_f_zero_hom_single_single (k := k) (H := S) y 1 1,
    barResolution_π_f_zero_hom_single_single (k := k) (H := G) (S.subtype ∘ y) 1 1]

set_option maxHeartbeats 3200000 in
theorem coindIso_hom_eq (A : Rep.{u} k S) (n : ℕ)
    (ev : Rep.res S.subtype (Rep.coind S.subtype A) ⟶ A)
    (hev : ∀ f : Rep.res S.subtype (Rep.coind S.subtype A), ev.hom f = (f : G → A) 1) :
    (groupCohomology.coindIso A n).hom =
      groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype (Rep.coind S.subtype A))) n ≫
        groupCohomology.map (MonoidHom.id S) ev n := by

  have hR : groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype (Rep.coind S.subtype A))) n ≫
      groupCohomology.map (MonoidHom.id S) ev n = groupCohomology.map S.subtype ev n := by
    rw [← groupCohomology.map_comp]
    rfl
  rw [hR]

  have hq : (isoOfQuasiIsoAt (HomotopyEquiv.ofIso (groupCohomology.inhomogeneousCochainsIso A)).hom n).inv =
      HomologicalComplex.homologyMap (groupCohomology.inhomogeneousCochainsIso A).inv n := by
    apply Iso.inv_ext
    rw [isoOfQuasiIsoAt_hom]
    show HomologicalComplex.homologyMap (groupCohomology.inhomogeneousCochainsIso A).hom n ≫ _ = _
    rw [← HomologicalComplex.homologyMap_comp, Iso.hom_inv_id, HomologicalComplex.homologyMap_id]

  dsimp only [groupCohomology.coindIso, groupCohomologyIso, groupCohomologyIsoExt, Rep.barResolution.extIso,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Functor.mapIso_hom, Functor.mapIso_inv]
  rw [HomologicalComplex.homologyFunctor_map, hq]
  erw [reassoc_of% (isoExt_inv_comp_isoExt_hom A n (barInclusion k G S) (barInclusion_comp_π k G S))]
  change HomologicalComplex.homologyMap
        ((groupCohomology.inhomogeneousCochainsIso (Rep.coind S.subtype A)).hom ≫
          (groupCohomology.linearYonedaObjResProjectiveResolutionIso (Rep.barResolution k G) A).inv) n ≫
      HomologicalComplex.homologyMap (precomp A (barInclusion k G S)) n ≫
        HomologicalComplex.homologyMap (groupCohomology.inhomogeneousCochainsIso A).inv n =
    groupCohomology.map S.subtype ev n
  erw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
  erw [Category.assoc, cochain_identity A ev hev]

end Bar

end ShapiroRes
p2m_reactivate "P2MW.S_groupCohomology_coindIso_hom_eq_map_subtype_comp_map_eval_one.ShapiroRes"

universe u in
set_option maxHeartbeats 3200000 in
theorem solution
    {k G : Type u} [CommRing k] [Group G] {S : Subgroup G} (A : Rep k S) (n : ℕ)
    (ev : Rep.res S.subtype (Rep.coind S.subtype A) ⟶ A)
    (hev : ∀ f : Rep.res S.subtype (Rep.coind S.subtype A), ev.hom f = (f : G → A) 1) :
    (groupCohomology.coindIso A n).hom =
      groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype (Rep.coind S.subtype A))) n ≫
        groupCohomology.map (MonoidHom.id S) ev n :=
  ShapiroRes.coindIso_hom_eq A n ev hev

end S_groupCohomology_coindIso_hom_eq_map_subtype_comp_map_eval_one
end P2MW
export P2MW.S_groupCohomology_coindIso_hom_eq_map_subtype_comp_map_eval_one (solution)
