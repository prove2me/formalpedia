-- Prove2me | solution 1 for groupCohomology.exists_continuousH2Sr_trivial_tensor_linearEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/24f28936-71c1-5c7d-9c26-a3da645515b0

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

namespace P2MW.S_groupCohomology_exists_continuousH2Sr_trivial_tensor_linearEquiv

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module groupCohomology ExtCitation"
open scoped TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 1600000
set_option Elab.async false

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module groupCohomology ExtCitation"
open scoped TensorProduct

set_option linter.unusedSectionVars false

namespace TrivCoef2

variable {k : Type} [Field k] {G : Type} [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (S : Finset Nat.Primes)
  (V : Type) [AddCommGroup V] [Module k V] [FiniteDimensional k V] (X : Rep.{0} k G)

local notation "T" => (Rep.trivial k G V)

noncomputable def ιRep (v : V) : X ⟶ (T ⊗ X : Rep.{0} k G) :=
  Rep.ofHom ⟨TensorProduct.mk k V X v, fun g => by
    apply LinearMap.ext; intro x
    show v ⊗ₜ[k] X.ρ g x = (T ⊗ X : Rep.{0} k G).ρ g (v ⊗ₜ[k] x)
    rw [Rep.tensor_ρ, Representation.tprod_apply, TensorProduct.map_tmul]
    rfl⟩

lemma ιRep_hom_apply (v : V) (x : X) : (ιRep V X v).hom x = v ⊗ₜ[k] x := rfl

noncomputable def πRep (ℓ : V →ₗ[k] k) : (T ⊗ X : Rep.{0} k G) ⟶ X :=
  Rep.ofHom ⟨TensorProduct.lift ((LinearMap.lsmul k X).comp ℓ), fun g => by
    apply TensorProduct.ext'
    intro v x
    show TensorProduct.lift ((LinearMap.lsmul k X).comp ℓ) ((T ⊗ X : Rep.{0} k G).ρ g (v ⊗ₜ[k] x)) =
      X.ρ g (TensorProduct.lift ((LinearMap.lsmul k X).comp ℓ) (v ⊗ₜ[k] x))
    rw [Rep.tensor_ρ, Representation.tprod_apply, TensorProduct.map_tmul, TensorProduct.lift.tmul, TensorProduct.lift.tmul]
    show ℓ (Representation.trivial k G V g v) • X.ρ g x = X.ρ g (ℓ v • x)
    rw [map_smul]; rfl⟩

lemma πRep_hom_tmul (ℓ : V →ₗ[k] k) (v : V) (x : X) : (πRep V X ℓ).hom (v ⊗ₜ[k] x) = ℓ v • x :=
  TensorProduct.lift.tmul v x

local notation "H" => continuousH2Sr r S
local notation "Hmap" => continuousH2SrMapHom S r

lemma coe_map {A B : Rep.{0} k G} (φ : A ⟶ B) (z : ↥(levelCocyclesSr₂ r S A)) (st : G × G) :
    ((levelCocyclesSr₂Map (MonoidHom.id G) (fun _ => rfl) S φ.hom.toLinearMap (fun g a => Rep.hom_comm_apply φ g a) z :
      ↥(levelCocyclesSr₂ r S B)) : G × G → B) st = φ.hom ((z : G × G → A) st) := rfl

noncomputable def ΨL : V →ₗ[k] (continuousH2Sr r S X →ₗ[k] continuousH2Sr r S (T ⊗ X : Rep.{0} k G)) where
  toFun v := continuousH2SrMapHom S r (ιRep V X v)
  map_add' v w := by
    apply Submodule.linearMap_qext
    apply LinearMap.ext; intro z
    show continuousH2SrMapHom S r (ιRep V X (v + w)) (continuousH2Srπ r S X z) =
      continuousH2SrMapHom S r (ιRep V X v) (continuousH2Srπ r S X z) + continuousH2SrMapHom S r (ιRep V X w) (continuousH2Srπ r S X z)
    rw [continuousH2SrMapHom_continuousH2Srπ, continuousH2SrMapHom_continuousH2Srπ, continuousH2SrMapHom_continuousH2Srπ, ← map_add]
    congr 1
    apply Subtype.ext; funext st
    rw [Submodule.coe_add, Pi.add_apply, coe_map, coe_map, coe_map, ιRep_hom_apply, ιRep_hom_apply, ιRep_hom_apply,
      TensorProduct.add_tmul]
  map_smul' c v := by
    apply Submodule.linearMap_qext
    apply LinearMap.ext; intro z
    show continuousH2SrMapHom S r (ιRep V X (c • v)) (continuousH2Srπ r S X z) =
      c • continuousH2SrMapHom S r (ιRep V X v) (continuousH2Srπ r S X z)
    rw [continuousH2SrMapHom_continuousH2Srπ, continuousH2SrMapHom_continuousH2Srπ, ← map_smul]
    congr 1

noncomputable def Ψ : V ⊗[k] continuousH2Sr r S X →ₗ[k] continuousH2Sr r S (T ⊗ X : Rep.{0} k G) :=
  TensorProduct.lift (ΨL r S V X)

lemma Ψ_tmul (v : V) (z : ↥(levelCocyclesSr₂ r S X)) :
    Ψ r S V X (v ⊗ₜ[k] continuousH2Srπ r S X z) = continuousH2SrMapHom S r (ιRep V X v) (continuousH2Srπ r S X z) :=
  TensorProduct.lift.tmul v _

section Basis
variable {ι : Type} [Fintype ι] (b : Basis ι k V)

noncomputable def Φ : continuousH2Sr r S (T ⊗ X : Rep.{0} k G) →ₗ[k] V ⊗[k] continuousH2Sr r S X :=
  ∑ i, (TensorProduct.mk k V (continuousH2Sr r S X) (b i)).comp (continuousH2SrMapHom S r (πRep V X (b.coord i)))

lemma Φ_apply (h : continuousH2Sr r S (T ⊗ X : Rep.{0} k G)) :
    Φ r S V X b h = ∑ i, b i ⊗ₜ[k] continuousH2SrMapHom S r (πRep V X (b.coord i)) h := by
  simp [Φ]

lemma Φ_Ψ : (Φ r S V X b).comp (Ψ r S V X) = LinearMap.id := by
  apply TensorProduct.ext'
  intro v h
  obtain ⟨z, rfl⟩ := continuousH2Srπ_surjective r S X h
  rw [LinearMap.comp_apply, LinearMap.id_apply, Ψ_tmul, Φ_apply]

  have key : ∀ i, continuousH2SrMapHom S r (πRep V X (b.coord i))
      (continuousH2SrMapHom S r (ιRep V X v) (continuousH2Srπ r S X z)) = b.coord i v • continuousH2Srπ r S X z := by
    intro i
    rw [continuousH2SrMapHom_continuousH2Srπ, continuousH2SrMapHom_continuousH2Srπ, ← map_smul]
    congr 1
  simp only [key, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Basis.coord_apply]
  rw [← TensorProduct.sum_tmul, b.sum_repr v]

lemma sum_ι_π (m : (T ⊗ X : Rep.{0} k G)) : ∑ i, (ιRep V X (b i)).hom ((πRep V X (b.coord i)).hom m) = m := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul v x =>
    have h1 : ∀ i, (ιRep V X (b i)).hom ((πRep V X (b.coord i)).hom (v ⊗ₜ[k] x)) = (b.repr v i • b i) ⊗ₜ[k] x := fun i => by
      rw [πRep_hom_tmul, ιRep_hom_apply, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Basis.coord_apply]
    simp only [h1]
    rw [← TensorProduct.sum_tmul, b.sum_repr v]
  | add m m' hm hm' =>
    simp only [map_add, Finset.sum_add_distrib, hm, hm']

end Basis
end TrivCoef2

namespace TrivCoef2

variable {k : Type} [Field k] {G : Type} [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (S : Finset Nat.Primes)
  (V : Type) [AddCommGroup V] [Module k V] [FiniteDimensional k V] (X : Rep.{0} k G)

local notation "T" => (Rep.trivial k G V)

section Basis2
variable {ι : Type} [Fintype ι] (b : Basis ι k V)

lemma Ψ_Φ : (Ψ r S V X).comp (Φ r S V X b) = LinearMap.id := by
  apply Submodule.linearMap_qext
  apply LinearMap.ext; intro w
  show Ψ r S V X (Φ r S V X b (continuousH2Srπ r S _ w)) = continuousH2Srπ r S _ w
  rw [Φ_apply, map_sum]
  simp only [continuousH2SrMapHom_continuousH2Srπ, Ψ_tmul]
  rw [← map_sum]
  congr 1
  apply Subtype.ext; funext st
  rw [Submodule.coe_sum, Finset.sum_apply]
  simp only [coe_map]
  exact sum_ι_π V X b ((w : G × G → (T ⊗ X : Rep.{0} k G)) st)

noncomputable def Θ : continuousH2Sr r S (T ⊗ X : Rep.{0} k G) ≃ₗ[k] V ⊗[k] continuousH2Sr r S X :=
  LinearEquiv.ofLinear (Φ r S V X b) (Ψ r S V X) (Φ_Ψ r S V X b) (Ψ_Φ r S V X b)

lemma Ψ_natural (φ : V →ₗ[k] V) (ψ : X ⟶ X) (e : (T ⊗ X : Rep.{0} k G) ⟶ (T ⊗ X : Rep.{0} k G))
    (he : ∀ (v : V) (x : X), e.hom (v ⊗ₜ[k] x) = φ v ⊗ₜ[k] ψ.hom x) :
    (continuousH2SrMapHom S r e).comp (Ψ r S V X) =
      (Ψ r S V X).comp (TensorProduct.map φ (continuousH2SrMapHom S r ψ)) := by
  apply TensorProduct.ext'
  intro v h
  obtain ⟨z, rfl⟩ := continuousH2Srπ_surjective r S X h
  rw [LinearMap.comp_apply, LinearMap.comp_apply, TensorProduct.map_tmul, Ψ_tmul, continuousH2SrMapHom_continuousH2Srπ,
    continuousH2SrMapHom_continuousH2Srπ, continuousH2SrMapHom_continuousH2Srπ, Ψ_tmul, continuousH2SrMapHom_continuousH2Srπ]
  congr 1
  apply Subtype.ext; funext st
  rw [coe_map, coe_map, coe_map, coe_map, ιRep_hom_apply, ιRep_hom_apply, he]

lemma Θ_natural (φ : V →ₗ[k] V) (ψ : X ⟶ X) (e : (T ⊗ X : Rep.{0} k G) ⟶ (T ⊗ X : Rep.{0} k G))
    (he : ∀ (v : V) (x : X), e.hom (v ⊗ₜ[k] x) = φ v ⊗ₜ[k] ψ.hom x) :
    (Θ r S V X b).toLinearMap.comp (continuousH2SrMapHom S r e) =
      (TensorProduct.map φ (continuousH2SrMapHom S r ψ)).comp (Θ r S V X b).toLinearMap := by
  have h1 : (Θ r S V X b).toLinearMap.comp (Ψ r S V X) = LinearMap.id := Φ_Ψ r S V X b
  have h2 : (Ψ r S V X).comp (Θ r S V X b).toLinearMap = LinearMap.id := Ψ_Φ r S V X b
  calc (Θ r S V X b).toLinearMap.comp (continuousH2SrMapHom S r e)
      = ((Θ r S V X b).toLinearMap.comp (continuousH2SrMapHom S r e)).comp ((Ψ r S V X).comp (Θ r S V X b).toLinearMap) := by
        rw [h2, LinearMap.comp_id]
    _ = (Θ r S V X b).toLinearMap.comp (((continuousH2SrMapHom S r e).comp (Ψ r S V X)).comp (Θ r S V X b).toLinearMap) := by
        simp only [LinearMap.comp_assoc]
    _ = (Θ r S V X b).toLinearMap.comp (((Ψ r S V X).comp (TensorProduct.map φ (continuousH2SrMapHom S r ψ))).comp
          (Θ r S V X b).toLinearMap) := by rw [Ψ_natural r S V X φ ψ e he]
    _ = (((Θ r S V X b).toLinearMap.comp (Ψ r S V X)).comp (TensorProduct.map φ (continuousH2SrMapHom S r ψ))).comp
          (Θ r S V X b).toLinearMap := by simp only [LinearMap.comp_assoc]
    _ = _ := by rw [h1, LinearMap.id_comp]

end Basis2
end TrivCoef2

open TrivCoef2 in

theorem solution
    {k : Type} [Field k] {G : Type} [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (S : Finset Nat.Primes)
    (V : Type) [AddCommGroup V] [Module k V] [FiniteDimensional k V] (X : Rep.{0} k G) :
    ∃ Θ : continuousH2Sr r S (Rep.trivial k G V ⊗ X) ≃ₗ[k] V ⊗[k] continuousH2Sr r S X,
      (∀ (v : V) (z : ↥(levelCocyclesSr₂ r S X)) (w : ↥(levelCocyclesSr₂ r S (Rep.trivial k G V ⊗ X))),
        (∀ st, (w : G × G → (Rep.trivial k G V ⊗ X : Rep.{0} k G)) st = v ⊗ₜ[k] (z : G × G → X) st) →
          Θ (continuousH2Srπ r S (Rep.trivial k G V ⊗ X) w) = v ⊗ₜ[k] continuousH2Srπ r S X z) ∧
      ∀ (φ : V →ₗ[k] V) (ψ : X ⟶ X) (e : (Rep.trivial k G V ⊗ X : Rep.{0} k G) ⟶ (Rep.trivial k G V ⊗ X : Rep.{0} k G)),
        (∀ (v : V) (x : X), e.hom (v ⊗ₜ[k] x) = φ v ⊗ₜ[k] ψ.hom x) →
          Θ.toLinearMap ∘ₗ continuousH2SrMapHom S r e = TensorProduct.map φ (continuousH2SrMapHom S r ψ) ∘ₗ Θ.toLinearMap := by
  let b := Module.finBasis k V
  refine ⟨Θ r S V X b, fun v z w hw => ?_, fun φ ψ e he => Θ_natural r S V X b φ ψ e he⟩

  have hΨ : Ψ r S V X (v ⊗ₜ[k] continuousH2Srπ r S X z) = continuousH2Srπ r S _ w := by
    rw [Ψ_tmul, continuousH2SrMapHom_continuousH2Srπ]
    congr 1
    apply Subtype.ext; funext st
    rw [coe_map, ιRep_hom_apply, hw st]
  rw [← hΨ]
  exact LinearMap.congr_fun (Φ_Ψ r S V X b) _

end S_groupCohomology_exists_continuousH2Sr_trivial_tensor_linearEquiv
end P2MW
export P2MW.S_groupCohomology_exists_continuousH2Sr_trivial_tensor_linearEquiv (solution)
