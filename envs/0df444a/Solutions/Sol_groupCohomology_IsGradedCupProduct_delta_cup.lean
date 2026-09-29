-- Prove2me | solution 1 for groupCohomology.IsGradedCupProduct.delta_cup
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/73108e54-a081-5344-a394-29b78357d2c7

import Mathlib
import Definitions.Def_GroupCohomology_CochainCup
import Definitions.Def_GroupCohomology_IsGradedCupProduct
import Theorems.Thm_groupCohomology_d_cochainCup_apply
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_IsGradedCupProduct_delta_cup

set_option autoImplicit false
universe u
p2m_open "CategoryTheory CategoryTheory.MonoidalCategory groupCohomology"

namespace P2mS26CupDelta

variable {k G : Type u} [CommRing k] [Group G]

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

theorem d_cast (A : Rep.{u} k G) (n m : ℕ) (h : n + 1 = m) (u : (Fin n → G) → A) :
    ((inhomogeneousCochains A).d n m).hom u
      = fun σ => (inhomogeneousCochains.d A n).hom u (fun j => σ (Fin.cast h j)) := by
  subst h
  funext σ
  simp

theorem cochainsMap_id_f_apply {A B : Rep.{u} k G} (φ : A ⟶ B) (n : ℕ) (x : (Fin n → G) → A) (σ : Fin n → G) :
    ((cochainsMap (MonoidHom.id G) φ).f n).hom x σ = φ.hom (x σ) := by
  rw [cochainsMap_f_hom]
  rfl

theorem hom_d_apply {A B : Rep.{u} k G} (φ : A ⟶ B) (n : ℕ) (x : (Fin n → G) → A) (τ : Fin (n + 1) → G) :
    φ.hom ((inhomogeneousCochains.d A n).hom x τ) = (inhomogeneousCochains.d B n).hom (fun σ => φ.hom (x σ)) τ := by
  simp only [inhomogeneousCochains.d_hom_apply, map_add, map_sum, map_smul, Rep.hom_comm_apply]

theorem whiskerRight_tmul {A A' : Rep.{u} k G} (φ : A ⟶ A') (B : Rep.{u} k G) (a : A) (b : B) :
    (φ ▷ B).hom (a ⊗ₜ[k] b) = φ.hom a ⊗ₜ[k] b := rfl

variable {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact)
include hX

theorem exists_lift (n : ℕ) (z : (Fin n → G) → X.X₃) :
    ∃ y : (Fin n → G) → X.X₂, ((cochainsMap (MonoidHom.id G) X.g).f n).hom y = z := by
  haveI := hX.epi_g
  exact (ModuleCat.epi_iff_surjective _).1 (cochainsMap_id_f_map_epi X.g n) z

theorem exists_preimage (v : X.X₂) (hv : X.g.hom v = 0) : ∃ u : X.X₁, X.f.hom u = v := by
  have h : LinearMap.range X.f.hom.toLinearMap = LinearMap.ker X.g.hom.toLinearMap :=
    (hX.exact.map (forget₂ (Rep k G) (ModuleCat k))).moduleCat_range_eq_ker
  have hv' : v ∈ LinearMap.range X.f.hom.toLinearMap := by
    rw [h]
    exact hv
  obtain ⟨u, hu⟩ := hv'
  exact ⟨u, hu⟩

end P2mS26CupDelta

open P2mS26CupDelta in
theorem solution {k G : Type u} [CommRing k] [Group G]
    {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact) (B : Rep.{u} k G)
    (hXB : (X.map (MonoidalCategory.tensorRight B)).ShortExact)
    (cup₁ : groupCohomology.GradedCupFamily X.X₁ B) (h₁ : groupCohomology.IsGradedCupProduct X.X₁ B cup₁)
    (cup₃ : groupCohomology.GradedCupFamily X.X₃ B) (h₃ : groupCohomology.IsGradedCupProduct X.X₃ B cup₃)
    (p q : ℕ) (x : groupCohomology X.X₃ p) (y : groupCohomology B q) :
    (groupCohomology.δ hXB (p + q) (p + 1 + q) (by omega)).hom (cup₃ p q x y)
      = cup₁ (p + 1) q ((groupCohomology.δ hX p (p + 1) rfl).hom x) y := by
  obtain ⟨z₀, rfl⟩ := π_surjective X.X₃ p x
  obtain ⟨y₀, rfl⟩ := π_surjective B q y

  have hz : (inhomogeneousCochains.d X.X₃ p).hom ((iCocycles X.X₃ p).hom z₀) = 0 := d_iCocycles _ _ z₀
  have hπ : (groupCohomology.π X.X₃ p).hom z₀
      = (groupCohomology.π X.X₃ p).hom (cocyclesMk ((iCocycles X.X₃ p).hom z₀) hz) :=
    congrArg _ (iCocycles_injective _ _ (i_cocyclesMk _ _).symm)

  obtain ⟨yt, hyt⟩ := exists_lift hX p ((iCocycles X.X₃ p).hom z₀)
  have hyt' : ∀ τ, X.g.hom (yt τ) = (iCocycles X.X₃ p).hom z₀ τ := fun τ => by
    rw [← cochainsMap_id_f_apply X.g p yt τ, hyt]
  have hg : ∀ τ, X.g.hom ((inhomogeneousCochains.d X.X₂ p).hom yt τ) = 0 := fun τ => by
    rw [hom_d_apply, show (fun σ => X.g.hom (yt σ)) = (iCocycles X.X₃ p).hom z₀ from funext hyt']
    exact congrFun hz τ
  choose w hw' using fun τ => exists_preimage hX ((inhomogeneousCochains.d X.X₂ p).hom yt τ) (hg τ)
  have hw : X.f.hom ∘ w = (inhomogeneousCochains X.X₂).d p (p + 1) yt := by
    rw [inhomogeneousCochains.d_def]
    funext τ
    exact hw' τ

  have key₁ : (groupCohomology.δ hX p (p + 1) rfl).hom
      ((groupCohomology.π X.X₃ p).hom (cocyclesMk ((iCocycles X.X₃ p).hom z₀) hz))
      = (groupCohomology.π X.X₁ (p + 1)).hom (cocyclesMkOfCompEqD hX hw) :=
    groupCohomology.δ_apply hX rfl ((iCocycles X.X₃ p).hom z₀)
      (by rw [inhomogeneousCochains.d_def]; exact hz) yt hyt w hw

  have key₂ := groupCohomology.δ_apply hXB (i := p + q) (j := p + 1 + q) (by omega)
    (cochainCup X.X₃ B p q ((iCocycles X.X₃ p).hom (cocyclesMk ((iCocycles X.X₃ p).hom z₀) hz))
      ((iCocycles B q).hom y₀))
    (by
      show ((inhomogeneousCochains (X.X₃ ⊗ B)).d (p + q) (p + 1 + q)).hom _ = 0
      rw [d_cast (X.X₃ ⊗ B) (p + q) (p + 1 + q) (by omega), i_cocyclesMk]
      funext σ
      exact congrFun (d_cup_eq_zero X.X₃ B p q z₀ y₀) _)
    (cochainCup X.X₂ B p q yt ((iCocycles B q).hom y₀))
    (by
      funext σ
      rw [cochainsMap_id_f_apply, i_cocyclesMk]
      show (X.g ▷ B).hom (cochainCup X.X₂ B p q yt ((iCocycles B q).hom y₀) σ) = _
      rw [cochainCup_apply, cochainCup_apply, whiskerRight_tmul, hyt'])
    (cochainCup X.X₁ B (p + 1) q w ((iCocycles B q).hom y₀))
    (by
      show (X.f ▷ B).hom ∘ _ = ((inhomogeneousCochains (X.X₂ ⊗ B)).d (p + q) (p + 1 + q)).hom _
      rw [d_cast (X.X₂ ⊗ B) (p + q) (p + 1 + q) (by omega)]
      funext σ
      simp only [Function.comp_apply]
      rw [groupCohomology.d_cochainCup_apply, d_iCocycles, map_zero, Pi.zero_apply, smul_zero, add_zero,
        cochainCup_apply, cochainCup_apply, whiskerRight_tmul, hw']
      simp only [Fin.cast_cast, Fin.cast_eq_self])
  rw [hπ, key₁, h₃.compat p q _ _ (d_cup_eq_zero _ _ _ _ _ _), h₁.compat (p + 1) q _ _ (d_cup_eq_zero _ _ _ _ _ _)]
  calc _ = _ := key₂
    _ = _ := congrArg _ (iCocycles_injective _ _ (by rw [i_cocyclesMk]; erw [i_cocyclesMk]; rw [i_cocyclesMk]))

end S_groupCohomology_IsGradedCupProduct_delta_cup
end P2MW
export P2MW.S_groupCohomology_IsGradedCupProduct_delta_cup (solution)
