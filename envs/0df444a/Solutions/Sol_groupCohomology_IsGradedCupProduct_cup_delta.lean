-- Prove2me | solution 1 for groupCohomology.IsGradedCupProduct.cup_delta
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/eafe98ae-048d-552d-bb0e-3f18d552e5ab

import Mathlib
import Definitions.Def_GroupCohomology_CochainCup
import Definitions.Def_GroupCohomology_IsGradedCupProduct
import Theorems.Thm_groupCohomology_d_cochainCup_apply
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_IsGradedCupProduct_cup_delta

set_option autoImplicit false
universe u
p2m_open "CategoryTheory CategoryTheory.MonoidalCategory groupCohomology"

namespace P2mS26CupDeltaR

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

theorem whiskerLeft_tmul (A : Rep.{u} k G) {B B' : Rep.{u} k G} (φ : B ⟶ B') (a : A) (b : B) :
    (A ◁ φ).hom (a ⊗ₜ[k] b) = a ⊗ₜ[k] φ.hom b := rfl

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

end P2mS26CupDeltaR

open P2mS26CupDeltaR in
theorem solution {k G : Type u} [CommRing k] [Group G]
    (A : Rep.{u} k G) {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact)
    (hAX : (X.map (MonoidalCategory.tensorLeft A)).ShortExact)
    (cup₁ : groupCohomology.GradedCupFamily A X.X₁) (h₁ : groupCohomology.IsGradedCupProduct A X.X₁ cup₁)
    (cup₃ : groupCohomology.GradedCupFamily A X.X₃) (h₃ : groupCohomology.IsGradedCupProduct A X.X₃ cup₃)
    (p q : ℕ) (x : groupCohomology A p) (y : groupCohomology X.X₃ q) :
    (groupCohomology.δ hAX (p + q) (p + q + 1) rfl).hom (cup₃ p q x y)
      = ((-1 : k) ^ p) • cup₁ p (q + 1) x ((groupCohomology.δ hX q (q + 1) rfl).hom y) := by
  obtain ⟨x₀, rfl⟩ := π_surjective A p x
  obtain ⟨z₀, rfl⟩ := π_surjective X.X₃ q y
  have hz : (inhomogeneousCochains.d X.X₃ q).hom ((iCocycles X.X₃ q).hom z₀) = 0 := d_iCocycles _ _ z₀
  have hπ : (groupCohomology.π X.X₃ q).hom z₀
      = (groupCohomology.π X.X₃ q).hom (cocyclesMk ((iCocycles X.X₃ q).hom z₀) hz) :=
    congrArg _ (iCocycles_injective _ _ (i_cocyclesMk _ _).symm)
  obtain ⟨zt, hzt⟩ := exists_lift hX q ((iCocycles X.X₃ q).hom z₀)
  have hzt' : ∀ τ, X.g.hom (zt τ) = (iCocycles X.X₃ q).hom z₀ τ := fun τ => by
    rw [← cochainsMap_id_f_apply X.g q zt τ, hzt]
  have hg : ∀ τ, X.g.hom ((inhomogeneousCochains.d X.X₂ q).hom zt τ) = 0 := fun τ => by
    rw [hom_d_apply, show (fun σ => X.g.hom (zt σ)) = (iCocycles X.X₃ q).hom z₀ from funext hzt']
    exact congrFun hz τ
  choose w hw' using fun τ => exists_preimage hX ((inhomogeneousCochains.d X.X₂ q).hom zt τ) (hg τ)
  have hw : X.f.hom ∘ w = (inhomogeneousCochains X.X₂).d q (q + 1) zt := by
    rw [inhomogeneousCochains.d_def]
    funext τ
    exact hw' τ
  have key₁ : (groupCohomology.δ hX q (q + 1) rfl).hom
      ((groupCohomology.π X.X₃ q).hom (cocyclesMk ((iCocycles X.X₃ q).hom z₀) hz))
      = (groupCohomology.π X.X₁ (q + 1)).hom (cocyclesMkOfCompEqD hX hw) :=
    groupCohomology.δ_apply hX rfl ((iCocycles X.X₃ q).hom z₀)
      (by rw [inhomogeneousCochains.d_def]; exact hz) zt hzt w hw
  have key₂ := groupCohomology.δ_apply hAX (i := p + q) (j := p + q + 1) rfl
    (cochainCup A X.X₃ p q ((iCocycles A p).hom x₀)
      ((iCocycles X.X₃ q).hom (cocyclesMk ((iCocycles X.X₃ q).hom z₀) hz)))
    (by
      show ((inhomogeneousCochains (A ⊗ X.X₃)).d (p + q) (p + q + 1)).hom _ = 0
      rw [inhomogeneousCochains.d_def, i_cocyclesMk]
      exact d_cup_eq_zero A X.X₃ p q x₀ z₀)
    (cochainCup A X.X₂ p q ((iCocycles A p).hom x₀) zt)
    (by
      funext σ
      rw [cochainsMap_id_f_apply, i_cocyclesMk]
      show (A ◁ X.g).hom (cochainCup A X.X₂ p q ((iCocycles A p).hom x₀) zt σ) = _
      rw [cochainCup_apply, cochainCup_apply, whiskerLeft_tmul, Rep.hom_comm_apply, hzt'])
    (((-1 : k) ^ p) • cochainCup A X.X₁ p (q + 1) ((iCocycles A p).hom x₀) w)
    (by
      show (A ◁ X.f).hom ∘ _ = ((inhomogeneousCochains (A ⊗ X.X₂)).d (p + q) (p + q + 1)).hom _
      rw [inhomogeneousCochains.d_def]
      funext σ
      simp only [Function.comp_apply, Pi.smul_apply]
      rw [groupCohomology.d_cochainCup_apply, d_iCocycles, map_zero, LinearMap.zero_apply, Pi.zero_apply, zero_add,
        cochainCup_apply, cochainCup_apply, map_smul, whiskerLeft_tmul, Rep.hom_comm_apply, hw'])
  have H₁ := d_cup_eq_zero A X.X₁ p (q + 1) x₀ (cocyclesMkOfCompEqD hX hw)
  rw [hπ, key₁, h₃.compat p q _ _ (d_cup_eq_zero _ _ _ _ _ _), h₁.compat p (q + 1) _ _ H₁]
  calc _ = _ := key₂
    _ = (groupCohomology.π (A ⊗ X.X₁) (p + (q + 1))).hom (((-1 : k) ^ p) • cocyclesMk _ H₁) :=
        congrArg _ (iCocycles_injective _ _ (by
          show (iCocycles (A ⊗ X.X₁) (p + (q + 1))).hom _ = (iCocycles (A ⊗ X.X₁) (p + (q + 1))).hom _
          rw [map_smul]
          erw [i_cocyclesMk, i_cocyclesMk, i_cocyclesMk]))
    _ = _ := map_smul _ _ _

end S_groupCohomology_IsGradedCupProduct_cup_delta
end P2MW
export P2MW.S_groupCohomology_IsGradedCupProduct_cup_delta (solution)
