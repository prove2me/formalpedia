-- Prove2me | solution 1 for groupCohomology.map_conj_eq_id
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/3dad1b02-e2fd-578d-aa78-9fd21a75ef33

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_map_conj_eq_id

set_option autoImplicit false

open CategoryTheory Opposite

namespace ShapiroRes

universe w v u' u

section General

variable {R : Type w} [Ring R] {C : Type u'} [Category.{v} C] [Abelian C] [Linear R C]

noncomputable def precompGen' {P Q : ChainComplex C ℕ} (φ : P ⟶ Q) (Y : C) :
    Q.linearYonedaObj R Y ⟶ P.linearYonedaObj R Y :=
  (HomologicalComplex.unopFunctor (ModuleCat R) (ComplexShape.down ℕ)).map
    ((((linearYoneda R C).obj Y).rightOp.mapHomologicalComplex (ComplexShape.down ℕ)).map φ).op

theorem precompGen'_f_apply {P Q : ChainComplex C ℕ} (φ : P ⟶ Q) (Y : C) (i : ℕ) (g : Q.X i ⟶ Y) :
    ((precompGen' (R := R) φ Y).f i).hom g = φ.f i ≫ g := rfl

theorem homologyMap_precompGen'_eq_of_homotopy {P Q : ChainComplex C ℕ} {T₁ T₂ : P ⟶ Q} (h : Homotopy T₁ T₂)
    (Y : C) (n : ℕ) :
    HomologicalComplex.homologyMap (precompGen' (R := R) T₁ Y) n =
      HomologicalComplex.homologyMap (precompGen' (R := R) T₂ Y) n := by
  have hψ := (((linearYoneda R C).obj Y).rightOp.mapHomotopy h).homologyMap_eq n
  have e₁ := (Iso.inv_comp_eq _).mpr (HomologicalComplex.homologyOp_hom_naturality (precompGen' (R := R) T₁ Y) n)
  have e₂ := (Iso.inv_comp_eq _).mpr (HomologicalComplex.homologyOp_hom_naturality (precompGen' (R := R) T₂ Y) n)
  apply Quiver.Hom.op_inj
  rw [← e₁, ← e₂]
  congr 2

noncomputable def homotopyIdOfCompπ {X : C} (P : ProjectiveResolution X) (T : P.complex ⟶ P.complex)
    (hT : T ≫ P.π = P.π) : Homotopy T (𝟙 P.complex) :=
  ProjectiveResolution.liftHomotopy (𝟙 X) T (𝟙 P.complex)
    (by rw [hT, CategoryTheory.Functor.map_id, Category.comp_id])
    (by rw [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp])

end General

section RepPrecomp

variable {k H : Type u} [CommRing k] [Group H]

noncomputable def precomp (A : Rep.{u} k H) {P Q : ChainComplex (Rep.{u} k H) ℕ} (φ : P ⟶ Q) :
    Q.linearYonedaObj k A ⟶ P.linearYonedaObj k A where
  f i := ModuleCat.ofHom (Linear.leftComp k A (φ.f i))
  comm' i j hij := by
    ext g
    show P.d j i ≫ (φ.f i ≫ g) = φ.f j ≫ (Q.d j i ≫ g)
    rw [← Category.assoc, ← Category.assoc, φ.comm]

theorem precomp_f_apply (A : Rep.{u} k H) {P Q : ChainComplex (Rep.{u} k H) ℕ} (φ : P ⟶ Q) (i : ℕ) (g : Q.X i ⟶ A) :
    (precomp A φ).f i g = φ.f i ≫ g := rfl

theorem precomp_eq_precompGen' (A : Rep.{u} k H) {P Q : ChainComplex (Rep.{u} k H) ℕ} (φ : P ⟶ Q) :
    precomp A φ = precompGen' φ A := by
  ext i g
  rfl

theorem homologyMap_precomp_eq_of_homotopy (A : Rep.{u} k H) {P Q : ChainComplex (Rep.{u} k H) ℕ}
    {T₁ T₂ : P ⟶ Q} (h : Homotopy T₁ T₂) (n : ℕ) :
    HomologicalComplex.homologyMap (precomp A T₁) n = HomologicalComplex.homologyMap (precomp A T₂) n := by
  rw [precomp_eq_precompGen', precomp_eq_precompGen']
  exact homologyMap_precompGen'_eq_of_homotopy h A n

theorem precomp_id (A : Rep.{u} k H) (P : ChainComplex (Rep.{u} k H) ℕ) : precomp A (𝟙 P) = 𝟙 _ := by
  ext i g
  show (𝟙 P : P ⟶ P).f i ≫ g = g
  rw [HomologicalComplex.id_f, Category.id_comp]

noncomputable def homotopyIdOfCompπRep {X : Rep.{u} k H} (P : ProjectiveResolution X) (T : P.complex ⟶ P.complex)
    (hT : T ≫ P.π = P.π) : Homotopy T (𝟙 P.complex) :=
  homotopyIdOfCompπ P T hT

theorem homologyMap_precomp_eq_id {X : Rep.{u} k H} (A : Rep.{u} k H) (P : ProjectiveResolution X)
    (T : P.complex ⟶ P.complex) (hT : T ≫ P.π = P.π) (n : ℕ) :
    HomologicalComplex.homologyMap (precomp A T) n = 𝟙 _ := by
  rw [homologyMap_precomp_eq_of_homotopy A (homotopyIdOfCompπ P T hT) n, precomp_id,
    HomologicalComplex.homologyMap_id]

end RepPrecomp

end ShapiroRes

namespace ConjBar

open ShapiroRes

universe u

variable {k G : Type u} [CommRing k] [Group G]

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

noncomputable def conjBarF (g : G) (n : ℕ) : Rep.free k G (Fin n → G) ⟶ Rep.free k G (Fin n → G) :=
  Rep.freeLift k G (Rep.free k G (Fin n → G))
    (fun x => Finsupp.single ((MulAut.conj g) ∘ x) (MonoidAlgebra.single g⁻¹ 1))

theorem conjBarF_single_single (g : G) (n : ℕ) (x : Fin n → G) (h : G) (r : k) :
    (conjBarF (k := k) g n).hom (Finsupp.single x (MonoidAlgebra.single h r)) =
      Finsupp.single ((MulAut.conj g) ∘ x) (MonoidAlgebra.single (h * g⁻¹) r) := by
  rw [conjBarF, Rep.hom_ofHom, Representation.freeLift_single_single]
  simp

theorem barComplex_d_single_single (n : ℕ) (x : Fin (n + 1) → G) (h : G) :
    (Rep.barComplex.d k G n).hom (Finsupp.single x (MonoidAlgebra.single h 1)) =
      Finsupp.single (fun i => x i.succ) (MonoidAlgebra.single (h * x 0) 1) +
        Finset.univ.sum fun j : Fin (n + 1) =>
          Finsupp.single (Fin.contractNth j (· * ·) x) (MonoidAlgebra.single h ((-1 : k) ^ ((j : ℕ) + 1))) := by
  have h1 : (Finsupp.single x (MonoidAlgebra.single h 1) : Rep.free k G (Fin (n + 1) → G)) =
      (Rep.free k G (Fin (n + 1) → G)).ρ h (Finsupp.single x (MonoidAlgebra.single 1 1)) := by
    rw [Representation.free_single_single, mul_one]
  rw [h1, Rep.hom_comm_apply, Rep.barComplex.d_single, map_add, map_sum]
  congr 1
  · rw [Representation.free_single_single]
  · exact Finset.sum_congr rfl fun j _ => by rw [Representation.free_single_single, mul_one]

theorem conjBarF_comm (g : G) (n : ℕ) :
    conjBarF (k := k) g (n + 1) ≫ Rep.barComplex.d k G n = Rep.barComplex.d k G n ≫ conjBarF g n := by
  refine Rep.free_ext k G _ _ _ fun x => ?_
  erw [Rep.hom_comp, Rep.hom_comp, Representation.IntertwiningMap.comp_apply, Representation.IntertwiningMap.comp_apply]
  rw [conjBarF_single_single, one_mul, barComplex_d_single_single, Rep.barComplex.d_single, map_add, map_sum,
    conjBarF_single_single]
  congr 1
  · congr 2
    simp only [Function.comp_apply, MulAut.conj_apply]
    rw [mul_assoc, inv_mul_cancel_left]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [conjBarF_single_single, one_mul, Fin.comp_contractNth]
    intro a b
    exact map_mul (MulAut.conj g) a b

noncomputable def conjBar (k : Type u) [CommRing k] (g : G) :
    (Rep.barResolution k G).complex ⟶ (Rep.barResolution k G).complex where
  f n := conjBarF g n
  comm' i j hij := by
    obtain rfl : j + 1 = i := hij
    show conjBarF g (j + 1) ≫ (Rep.barComplex k G).d (j + 1) j = (Rep.barComplex k G).d (j + 1) j ≫ conjBarF g j
    rw [Rep.barComplex.d_def]
    exact conjBarF_comm (k := k) g j

theorem conjBar_f (g : G) (n : ℕ) : (conjBar k g).f n = conjBarF g n := rfl

theorem barResolution_π_f_zero_hom_single_single (x : Fin 0 → G) (h : G) (r : k) :
    ((Rep.barResolution k G).π.f 0).hom (Finsupp.single x (MonoidAlgebra.single h r)) = (r : k) := by
  unfold Rep.barResolution
  dsimp only
  rw [HomologicalComplex.comp_f]
  erw [Rep.hom_comp, Representation.IntertwiningMap.comp_apply]
  simp only [Rep.barComplex.isoStandardComplex, HomologicalComplex.Hom.isoOfComponents_hom_f, Iso.symm_hom]
  erw [diagonalSuccIsoFree_zero_inv_hom_single_single]
  rw [Rep.standardComplex.εToSingle₀]
  erw [ChainComplex.toSingle₀Equiv_symm_apply_f_zero]
  exact standardComplex_ε_hom_single _ _

set_option maxHeartbeats 3200000 in
theorem conjBar_comp_π (g : G) : conjBar k g ≫ (Rep.barResolution k G).π = (Rep.barResolution k G).π := by
  refine HomologicalComplex.to_single_hom_ext ?_
  rw [HomologicalComplex.comp_f, conjBar_f]
  refine Rep.free_ext k G _ _ _ fun y => ?_
  change ((Rep.barResolution k G).π.f 0).hom ((conjBarF g 0).hom (Finsupp.single y (MonoidAlgebra.single 1 1))) = _
  rw [conjBarF_single_single (k := k) g 0 y 1 1]
  rw [one_mul]
  erw [barResolution_π_f_zero_hom_single_single (k := k) ((MulAut.conj g) ∘ y) g⁻¹ 1,
    barResolution_π_f_zero_hom_single_single (k := k) y 1 1]

theorem freeLiftLEquiv_symm_hom {α : Type u} (X : Rep.{u} k G) (F : α → X) :
    ((Rep.freeLiftLEquiv k G α X).symm F).hom = Representation.freeLift X.ρ F := rfl

theorem cochain_identity (M : Rep.{u} k G) (g : G) (φ : Rep.res (MulAut.conj g).toMonoidHom M ⟶ M)
    (hφ : ∀ m : Rep.res (MulAut.conj g).toMonoidHom M, φ.hom m = M.ρ g⁻¹ m) :
    (groupCohomology.inhomogeneousCochainsIso M).hom ≫ precomp M (conjBar k g) =
      groupCohomology.cochainsMap (MulAut.conj g).toMonoidHom φ ≫ (groupCohomology.inhomogeneousCochainsIso M).hom := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  refine ModuleCat.hom_ext (LinearMap.ext fun u => ?_)
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply]
  rw [groupCohomology.cochainsMap_f]
  simp only [groupCohomology.inhomogeneousCochainsIso, HomologicalComplex.Hom.isoOfComponents_hom_f, Iso.symm_hom,
    LinearEquiv.toModuleIso_inv, precomp_f_apply]
  show (conjBar k g).f n ≫ (Rep.freeLiftLEquiv k G (Fin n → G) M).symm u =
    (Rep.freeLiftLEquiv k G (Fin n → G) M).symm (φ.hom.toLinearMap.compLeft (Fin n → G)
      (LinearMap.funLeft k M (fun x : Fin n → G => ((MulAut.conj g).toMonoidHom ∘ x)) u))
  refine Rep.free_ext k G _ _ _ fun x => ?_
  erw [Rep.hom_comp, Representation.IntertwiningMap.comp_apply]
  rw [conjBar_f]
  erw [conjBarF_single_single (k := k) g n x 1 1]
  rw [one_mul]
  erw [freeLiftLEquiv_symm_hom, freeLiftLEquiv_symm_hom, Representation.freeLift_single_single,
    Representation.freeLift_single_single]
  rw [one_smul, one_smul, map_one, Module.End.one_apply]
  simp only [LinearMap.compLeft_apply, Function.comp_apply, LinearMap.funLeft_apply,
    Representation.IntertwiningMap.coe_toLinearMap, hφ]
  rfl

theorem map_conj_eq_id (M : Rep.{u} k G) (g : G) (n : ℕ) (φ : Rep.res (MulAut.conj g).toMonoidHom M ⟶ M)
    (hφ : ∀ m : Rep.res (MulAut.conj g).toMonoidHom M, φ.hom m = M.ρ g⁻¹ m) :
    groupCohomology.map (MulAut.conj g).toMonoidHom φ n = 𝟙 (groupCohomology M n) := by
  have hT : HomologicalComplex.homologyMap (precomp M (conjBar k g)) n = 𝟙 _ :=
    homologyMap_precomp_eq_id M (Rep.barResolution k G) (conjBar k g) (conjBar_comp_π g) n
  have hc : groupCohomology.cochainsMap (MulAut.conj g).toMonoidHom φ =
      ((groupCohomology.inhomogeneousCochainsIso M).hom ≫ precomp M (conjBar k g)) ≫
        (groupCohomology.inhomogeneousCochainsIso M).inv :=
    (Iso.eq_comp_inv (groupCohomology.inhomogeneousCochainsIso M)).mpr (cochain_identity M g φ hφ).symm
  show HomologicalComplex.homologyMap (groupCohomology.cochainsMap (MulAut.conj g).toMonoidHom φ) n = _
  rw [hc, HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp]
  erw [hT, Category.comp_id, ← HomologicalComplex.homologyMap_comp, Iso.hom_inv_id, HomologicalComplex.homologyMap_id]
  rfl

end ConjBar
p2m_reactivate "P2MW.S_groupCohomology_map_conj_eq_id.ConjBar"

universe u in
theorem solution
    {k G : Type u} [CommRing k] [Group G] (M : Rep k G) (g : G) (n : ℕ)
    (φ : Rep.res (MulAut.conj g).toMonoidHom M ⟶ M)
    (hφ : ∀ m : Rep.res (MulAut.conj g).toMonoidHom M, φ.hom m = M.ρ g⁻¹ m) :
    groupCohomology.map (MulAut.conj g).toMonoidHom φ n = 𝟙 (groupCohomology M n) :=
  ConjBar.map_conj_eq_id M g n φ hφ

end S_groupCohomology_map_conj_eq_id
end P2MW
export P2MW.S_groupCohomology_map_conj_eq_id (solution)
