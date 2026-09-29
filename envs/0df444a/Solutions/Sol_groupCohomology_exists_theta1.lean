-- Prove2me | solution 1 for groupCohomology.exists_theta1
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/1d8d9e72-2f68-5b19-8f74-e7912ef56f9b

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Definitions.Def_GroupCohomology_ContinuousH1
import Definitions.Def_GroupCohomology_CupProduct
import Definitions.Def_GroupCohomology_ContinuousDuality
import Theorems.Thm_groupCohomology_cup_mem_levelCocycles2
import Theorems.Thm_groupCohomology_cup_mem_levelCoboundaries2_of_mem_coboundaries1_left
import Theorems.Thm_groupCohomology_cup_mem_levelCoboundaries2_of_mem_coboundaries1_right
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_exists_theta1

set_option autoImplicit false
set_option maxHeartbeats 1600000

universe u

open CategoryTheory groupCohomology

namespace P2mS26LD7e
variable {k G : Type u} [CommRing k] [Group G] {r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)}
variable (r) in

noncomputable def πlc (M : Rep.{u} k G) : levelCocycles₁ r M →ₗ[k] continuousH1 r M :=
  ((H1π M).hom ∘ₗ (levelCocycles₁ r M).subtype).codRestrict _ fun c => Submodule.mem_map_of_mem c.2
lemma coe_πlc (M : Rep.{u} k G) (c : levelCocycles₁ r M) : (πlc r M c : H1 M) = (H1π M).hom (c : cocycles₁ M) := rfl
lemma πlc_surjective (M : Rep.{u} k G) : Function.Surjective (πlc r M) := by
  intro x
  obtain ⟨c, hc, hx⟩ := (mem_continuousH1_iff r M _).1 x.2
  exact ⟨⟨c, hc⟩, Subtype.ext hx⟩
lemma H1π_hom_eq_zero_iff {M : Rep.{u} k G} (c : cocycles₁ M) : (H1π M).hom c = 0 ↔ (c : G → M) ∈ coboundaries₁ M :=
  H1π_eq_zero_iff c
end P2mS26LD7e
open P2mS26LD7e in
theorem solution
    {k G : Type u} [CommRing k] [Group G]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    {M D N : Rep.{u} k G} (φ : M →ₗ[k] D →ₗ[k] N) (hφ : Rep.IsEquivariantBilinear M D N φ)
    (hsmD : ∀ x : D, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s, r s ∈ F.fixingSubgroup → D.ρ s x = x)
    (inv : continuousH2 r N →ₗ[k] k) :
    ∃ θ₁ : continuousH1 r M →ₗ[k] Module.Dual k (continuousH1 r D), IsTheta1 r φ inv θ₁ := by
  classical

  have memT : ∀ (f : levelCocycles₁ r M) (g : levelCocycles₁ r D),
      (cup φ hφ (f : cocycles₁ M) (g : cocycles₁ D) : G × G → N) ∈ levelCocycles₂ r N :=
    fun f g => groupCohomology.cup_mem_levelCocycles2 r φ hφ hsmD _ _ f.2 g.2
  let T : levelCocycles₁ r M →ₗ[k] levelCocycles₁ r D →ₗ[k] levelCocycles₂ r N :=
    LinearMap.mk₂ k (fun f g => ⟨_, memT f g⟩)
      (fun f f' g => by
        apply Subtype.ext
        show ((cup φ hφ ((f : cocycles₁ M) + f') (g : cocycles₁ D) : cocycles₂ N) : G × G → N)
          = (cup φ hφ (f : cocycles₁ M) (g : cocycles₁ D) : G × G → N) + (cup φ hφ (f' : cocycles₁ M) (g : cocycles₁ D) : G × G → N)
        rw [map_add, LinearMap.add_apply]; rfl)
      (fun c f g => by
        apply Subtype.ext
        show ((cup φ hφ (c • (f : cocycles₁ M)) (g : cocycles₁ D) : cocycles₂ N) : G × G → N)
          = c • (cup φ hφ (f : cocycles₁ M) (g : cocycles₁ D) : G × G → N)
        rw [map_smul, LinearMap.smul_apply]; rfl)
      (fun f g g' => by
        apply Subtype.ext
        show ((cup φ hφ (f : cocycles₁ M) ((g : cocycles₁ D) + g') : cocycles₂ N) : G × G → N)
          = (cup φ hφ (f : cocycles₁ M) (g : cocycles₁ D) : G × G → N) + (cup φ hφ (f : cocycles₁ M) (g' : cocycles₁ D) : G × G → N)
        rw [map_add]; rfl)
      (fun c f g => by
        apply Subtype.ext
        show ((cup φ hφ (f : cocycles₁ M) (c • (g : cocycles₁ D)) : cocycles₂ N) : G × G → N)
          = c • (cup φ hφ (f : cocycles₁ M) (g : cocycles₁ D) : G × G → N)
        rw [map_smul]; rfl)

  let B₀ : levelCocycles₁ r M →ₗ[k] levelCocycles₁ r D →ₗ[k] k := T.compr₂ (inv ∘ₗ continuousH2π r N)
  have B₀_apply : ∀ f g, B₀ f g = inv (continuousH2π r N ⟨_, memT f g⟩) := fun _ _ => rfl

  have fibM : ∀ f f' : levelCocycles₁ r M, πlc r M f = πlc r M f' → ∀ g, B₀ f g = B₀ f' g := by
    intro f f' h g
    have hcob : (((f : cocycles₁ M) - (f' : cocycles₁ M) : cocycles₁ M) : G → M) ∈ coboundaries₁ M := by
      rw [← H1π_hom_eq_zero_iff, map_sub, sub_eq_zero]
      exact congrArg Subtype.val h
    rw [B₀_apply, B₀_apply, ← sub_eq_zero, ← map_sub, ← map_sub, ← inv.map_zero]
    congr 1
    rw [continuousH2π_eq_zero_iff]
    have hc := groupCohomology.cup_mem_levelCoboundaries2_of_mem_coboundaries1_left r φ hφ
      ((f : cocycles₁ M) - (f' : cocycles₁ M)) (g : cocycles₁ D) hcob g.2
    rw [map_sub, LinearMap.sub_apply] at hc
    exact hc
  have fibD : ∀ g g' : levelCocycles₁ r D, πlc r D g = πlc r D g' → ∀ f, B₀ f g = B₀ f g' := by
    intro g g' h f
    have hcob : (((g : cocycles₁ D) - (g' : cocycles₁ D) : cocycles₁ D) : G → D) ∈ coboundaries₁ D := by
      rw [← H1π_hom_eq_zero_iff, map_sub, sub_eq_zero]
      exact congrArg Subtype.val h
    obtain ⟨b, hb⟩ := hcob
    rw [B₀_apply, B₀_apply, ← sub_eq_zero, ← map_sub, ← map_sub, ← inv.map_zero]
    congr 1
    rw [continuousH2π_eq_zero_iff]
    have hc := groupCohomology.cup_mem_levelCoboundaries2_of_mem_coboundaries1_right r φ hφ
      (f : cocycles₁ M) ((g : cocycles₁ D) - (g' : cocycles₁ D)) f.2 b (hsmD b) (fun s => by rw [← hb, d₀₁_hom_apply])
    rw [map_sub] at hc
    exact hc
  let sM := Function.surjInv (πlc_surjective (r := r) M)
  let sD := Function.surjInv (πlc_surjective (r := r) D)
  have hsM : ∀ x, πlc r M (sM x) = x := Function.surjInv_eq (πlc_surjective (r := r) M)
  have hsD : ∀ y, πlc r D (sD y) = y := Function.surjInv_eq (πlc_surjective (r := r) D)
  let θ : continuousH1 r M →ₗ[k] Module.Dual k (continuousH1 r D) :=
    LinearMap.mk₂ k (fun x y => B₀ (sM x) (sD y))
      (fun x x' y => by
        show B₀ (sM (x + x')) (sD y) = B₀ (sM x) (sD y) + B₀ (sM x') (sD y)
        rw [fibM (sM (x + x')) (sM x + sM x') (by rw [map_add, hsM, hsM, hsM]), map_add, LinearMap.add_apply])
      (fun c x y => by
        show B₀ (sM (c • x)) (sD y) = c • B₀ (sM x) (sD y)
        rw [fibM (sM (c • x)) (c • sM x) (by rw [map_smul, hsM, hsM]), map_smul, LinearMap.smul_apply])
      (fun x y y' => by
        show B₀ (sM x) (sD (y + y')) = B₀ (sM x) (sD y) + B₀ (sM x) (sD y')
        rw [fibD (sD (y + y')) (sD y + sD y') (by rw [map_add, hsD, hsD, hsD]), map_add])
      (fun c x y => by
        show B₀ (sM x) (sD (c • y)) = c • B₀ (sM x) (sD y)
        rw [fibD (sD (c • y)) (c • sD y) (by rw [map_smul, hsD, hsD]), map_smul])
  refine ⟨θ, fun f hf g hg e he => ?_⟩
  have hx : (⟨(H1π M).hom f, H1π_mem_continuousH1 r M hf⟩ : continuousH1 r M) = πlc r M ⟨f, hf⟩ := rfl
  have hy : (⟨(H1π D).hom g, H1π_mem_continuousH1 r D hg⟩ : continuousH1 r D) = πlc r D ⟨g, hg⟩ := rfl
  rw [hx, hy]
  show B₀ (sM (πlc r M ⟨f, hf⟩)) (sD (πlc r D ⟨g, hg⟩)) = inv (continuousH2π r N e)
  rw [fibM (sM (πlc r M ⟨f, hf⟩)) ⟨f, hf⟩ (hsM _), fibD (sD (πlc r D ⟨g, hg⟩)) ⟨g, hg⟩ (hsD _), B₀_apply]
  congr 2
  apply Subtype.ext
  show ((cup φ hφ f g : cocycles₂ N) : G × G → N) = (e : G × G → N)
  funext st
  rw [he st, cup_coe]

end S_groupCohomology_exists_theta1
end P2MW
export P2MW.S_groupCohomology_exists_theta1 (solution)
