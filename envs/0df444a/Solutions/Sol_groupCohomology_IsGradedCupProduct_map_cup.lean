-- Prove2me | solution 1 for groupCohomology.IsGradedCupProduct.map_cup
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/9d6d3325-34b6-5b11-a41b-86bc7c687d38

import Mathlib
import Definitions.Def_GroupCohomology_CochainCup
import Definitions.Def_GroupCohomology_IsGradedCupProduct
import Theorems.Thm_groupCohomology_d_cochainCup_apply
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_IsGradedCupProduct_map_cup

set_option autoImplicit false
set_option maxHeartbeats 2400000
universe u
p2m_open "CategoryTheory CategoryTheory.MonoidalCategory groupCohomology"

namespace P2mS26CupMap

variable {k G H : Type u} [CommRing k] [Group G] [Group H]

theorem d_iCocycles (A : Rep.{u} k G) (n : ℕ) (x : cocycles A n) :
    (inhomogeneousCochains.d A n).hom ((iCocycles A n).hom x) = 0 := by
  have := congrArg (fun φ => φ.hom x) ((inhomogeneousCochains A).iCycles_d n (n + 1))
  simpa [ModuleCat.hom_comp] using this

theorem d_cup_eq_zero (A B : Rep.{u} k G) (p q : ℕ) (x : cocycles A p) (y : cocycles B q) :
    (inhomogeneousCochains.d (A ⊗ B) (p + q)).hom
      (cochainCup A B p q ((iCocycles A p).hom x) ((iCocycles B q).hom y)) = 0 := by
  funext σ
  rw [groupCohomology.d_cochainCup_apply, d_iCocycles, d_iCocycles, map_zero, map_zero, LinearMap.zero_apply,
    Pi.zero_apply, Pi.zero_apply, smul_zero, add_zero]

theorem π_surjective (A : Rep.{u} k G) (n : ℕ) : Function.Surjective (groupCohomology.π A n).hom :=
  (ModuleCat.epi_iff_surjective ((inhomogeneousCochains A).homologyπ n)).1 inferInstance

theorem iCocycles_injective (A : Rep.{u} k G) (n : ℕ) : Function.Injective (iCocycles A n).hom :=
  (ModuleCat.mono_iff_injective (iCocycles A n)).1 inferInstance

theorem i_cocyclesMk {A : Rep.{u} k G} {n : ℕ} (x : (Fin n → G) → A) (h) :
    (iCocycles A n).hom (cocyclesMk x h) = x :=
  iCocycles_mk x h

theorem π_map_hom (f : H →* G) {A : Rep.{u} k G} {A' : Rep.{u} k H} (φ : Rep.res f A ⟶ A') (n : ℕ) (z : cocycles A n) :
    (groupCohomology.map f φ n).hom ((groupCohomology.π A n).hom z)
      = (groupCohomology.π A' n).hom ((cocyclesMap f φ n).hom z) := by
  have := congrArg (fun ψ => ψ.hom z) (groupCohomology.π_map f φ n)
  simpa [ModuleCat.hom_comp] using this

theorem i_cocyclesMap (f : H →* G) {A : Rep.{u} k G} {A' : Rep.{u} k H} (φ : Rep.res f A ⟶ A') (n : ℕ) (z : cocycles A n) :
    (iCocycles A' n).hom ((cocyclesMap f φ n).hom z) = ((cochainsMap f φ).f n).hom ((iCocycles A n).hom z) := by
  have := congrArg (fun ψ => ψ.hom z) (HomologicalComplex.cyclesMap_i (cochainsMap f φ) n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
  exact this

theorem cochainsMap_f_apply (f : H →* G) {A : Rep.{u} k G} {A' : Rep.{u} k H} (φ : Rep.res f A ⟶ A') (n : ℕ)
    (x : (Fin n → G) → A) (σ : Fin n → H) :
    ((cochainsMap f φ).f n).hom x σ = φ.hom (x (f ∘ σ)) := by
  rw [cochainsMap_f_hom]
  rfl

theorem map_partialProd (f : H →* G) {n : ℕ} (τ : Fin n → H) (i : Fin (n + 1)) :
    Fin.partialProd (f ∘ τ) i = f (Fin.partialProd τ i) := by
  induction i using Fin.inductionOn with
  | zero => simp
  | succ i ih => rw [Fin.partialProd_succ, Fin.partialProd_succ, ih, map_mul, Function.comp_apply]

theorem tensorHom_tmul {A B A' B' : Rep.{u} k H} (φ : A ⟶ A') (ψ : B ⟶ B') (a : A) (b : B) :
    (φ ⊗ₘ ψ).hom (a ⊗ₜ[k] b) = φ.hom a ⊗ₜ[k] ψ.hom b := rfl

end P2mS26CupMap

open P2mS26CupMap in
theorem solution {k G H : Type u} [CommRing k] [Group G] [Group H]
    (f : H →* G) {A B : Rep.{u} k G} {A' B' : Rep.{u} k H} (φ : Rep.res f A ⟶ A') (ψ : Rep.res f B ⟶ B')
    (cup : groupCohomology.GradedCupFamily A B) (hcup : groupCohomology.IsGradedCupProduct A B cup)
    (cup' : groupCohomology.GradedCupFamily A' B') (hcup' : groupCohomology.IsGradedCupProduct A' B' cup')
    (p q : ℕ) (x : groupCohomology A p) (y : groupCohomology B q) :
    (groupCohomology.map f (φ ⊗ₘ ψ : Rep.res f (A ⊗ B) ⟶ A' ⊗ B') (p + q)).hom (cup p q x y)
      = cup' p q ((groupCohomology.map f φ p).hom x) ((groupCohomology.map f ψ q).hom y) := by
  obtain ⟨x₀, rfl⟩ := π_surjective A p x
  obtain ⟨y₀, rfl⟩ := π_surjective B q y
  rw [hcup.compat p q x₀ y₀ (d_cup_eq_zero A B p q x₀ y₀), π_map_hom, π_map_hom, π_map_hom,
    hcup'.compat p q _ _ (d_cup_eq_zero A' B' p q _ _)]
  congr 1
  apply iCocycles_injective
  rw [i_cocyclesMap, i_cocyclesMk, i_cocyclesMk, i_cocyclesMap, i_cocyclesMap]
  funext σ
  rw [cochainsMap_f_apply, cochainCup_apply, cochainCup_apply, cochainsMap_f_apply, cochainsMap_f_apply]
  erw [tensorHom_tmul]
  have hψ : ψ.hom (B.ρ (Fin.partialProd (cochainCupFst p q (f ∘ σ)) (Fin.last p))
      ((iCocycles B q).hom y₀ (cochainCupSnd p q (f ∘ σ))))
      = B'.ρ (Fin.partialProd (cochainCupFst p q σ) (Fin.last p))
          (ψ.hom ((iCocycles B q).hom y₀ (f ∘ cochainCupSnd p q σ))) := by
    have e : cochainCupFst p q (f ∘ σ) = f ∘ cochainCupFst p q σ := rfl
    rw [e, map_partialProd]
    exact Rep.hom_comm_apply ψ _ _
  rw [hψ]
  rfl

end S_groupCohomology_IsGradedCupProduct_map_cup
end P2MW
export P2MW.S_groupCohomology_IsGradedCupProduct_map_cup (solution)
