-- Prove2me | solution 1 for groupCohomology.exists_linearMap_levelCocycles1_continuousH2_eq_continuousH2pi_deltaCochain1
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/6af832c0-174b-53bb-839e-f75b0faba10e

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Definitions.Def_GroupCohomology_ContinuousH1
import Theorems.Thm_groupCohomology_deltaCochain1_mem_levelCocycles2
import Theorems.Thm_groupCohomology_preimageFun_comp_d12_sub_deltaCochain1_mem_levelCoboundaries2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_exists_linearMap_levelCocycles1_continuousH2_eq_continuousH2pi_deltaCochain1

set_option autoImplicit false

universe u

open CategoryTheory

open groupCohomology in
theorem solution {k G : Type u} [CommRing k] [Group G]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) {A B C : Rep.{u} k G} (φ : A ⟶ B) (ψ : B ⟶ C)
    (hφ : Function.Injective φ.hom) (hψ : Function.Surjective ψ.hom) (hex : ∀ b : B, ψ.hom b = 0 ↔ ∃ a : A, φ.hom a = b)
    (hsm : ∀ m : B, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s, r s ∈ F.fixingSubgroup → B.ρ s m = m) :
    ∃ δ : groupCohomology.levelCocycles₁ r C →ₗ[k] groupCohomology.continuousH2 r A,
      ∀ c : groupCohomology.levelCocycles₁ r C,
        ∃ h : groupCohomology.deltaCochain₁ φ ψ hψ ((c : groupCohomology.cocycles₁ C) : G → C)
            ∈ groupCohomology.levelCocycles₂ r A,
          δ c = groupCohomology.continuousH2π r A ⟨_, h⟩ := by
  have hσ : ∀ x : C, ψ.hom (Function.surjInv hψ x) = x := Function.surjInv_eq hψ
  have mem : ∀ c : levelCocycles₁ r C,
      deltaCochain₁ φ ψ hψ ((c : cocycles₁ C) : G → C) ∈ levelCocycles₂ r A := fun c =>
    groupCohomology.deltaCochain1_mem_levelCocycles2 r φ ψ hφ hψ hex hsm (c : cocycles₁ C) c.2

  have hφδ : ∀ (c : cocycles₁ C) (p : G × G),
      φ.hom (deltaCochain₁ φ ψ hψ c p) = (d₁₂ B).hom (Function.surjInv hψ ∘ c) p := by
    intro c p
    refine apply_preimageFun φ ((hex _).1 ?_)
    obtain ⟨g, h⟩ := p
    rw [d₁₂_hom_apply, map_add, map_sub, Rep.hom_comm_apply, Function.comp_apply, Function.comp_apply,
      Function.comp_apply, hσ, hσ, hσ, (mem_cocycles₁_iff (c : G → C)).1 c.2 g h]
    abel
  let f : levelCocycles₁ r C → continuousH2 r A := fun c => continuousH2π r A ⟨_, mem c⟩

  have lift : ∀ (c : levelCocycles₁ r C) (L : G → B) (hL : IsLevelConstant₁ r L)
      (hLc : ∀ g, ψ.hom (L g) = ((c : cocycles₁ C) : G → C) g)
      (hmem : preimageFun φ ∘ (d₁₂ B).hom L ∈ levelCocycles₂ r A),
      continuousH2π r A ⟨_, hmem⟩ = f c := by
    intro c L hL hLc hmem
    rw [← sub_eq_zero, ← map_sub, continuousH2π_eq_zero_iff]
    exact groupCohomology.preimageFun_comp_d12_sub_deltaCochain1_mem_levelCoboundaries2 r φ ψ hφ hψ hex
      (c : cocycles₁ C) c.2 L hL hLc
  have hadd : ∀ c c' : levelCocycles₁ r C, f (c + c') = f c + f c' := by
    intro c c'
    have hL : IsLevelConstant₁ r (Function.surjInv hψ ∘ ((c : cocycles₁ C) : G → C)
        + Function.surjInv hψ ∘ ((c' : cocycles₁ C) : G → C)) := (c.2.comp _).add (c'.2.comp _)
    have hLc : ∀ g, ψ.hom ((Function.surjInv hψ ∘ ((c : cocycles₁ C) : G → C)
        + Function.surjInv hψ ∘ ((c' : cocycles₁ C) : G → C)) g) = (((c + c' : levelCocycles₁ r C) : cocycles₁ C) : G → C) g := by
      intro g
      rw [Pi.add_apply, map_add, Function.comp_apply, Function.comp_apply, hσ, hσ]
      rfl
    have e : preimageFun φ ∘ (d₁₂ B).hom (Function.surjInv hψ ∘ ((c : cocycles₁ C) : G → C)
          + Function.surjInv hψ ∘ ((c' : cocycles₁ C) : G → C))
        = deltaCochain₁ φ ψ hψ ((c : cocycles₁ C) : G → C) + deltaCochain₁ φ ψ hψ ((c' : cocycles₁ C) : G → C) := by
      funext p
      apply hφ
      have lhs : φ.hom ((preimageFun φ ∘ (d₁₂ B).hom (Function.surjInv hψ ∘ ((c : cocycles₁ C) : G → C)
            + Function.surjInv hψ ∘ ((c' : cocycles₁ C) : G → C))) p)
          = (d₁₂ B).hom (Function.surjInv hψ ∘ ((c : cocycles₁ C) : G → C)) p
            + (d₁₂ B).hom (Function.surjInv hψ ∘ ((c' : cocycles₁ C) : G → C)) p := by
        rw [Function.comp_apply, map_add, Pi.add_apply]
        exact apply_preimageFun φ ⟨deltaCochain₁ φ ψ hψ ((c : cocycles₁ C) : G → C) p
          + deltaCochain₁ φ ψ hψ ((c' : cocycles₁ C) : G → C) p, by rw [map_add, hφδ, hφδ]⟩
      rw [lhs, Pi.add_apply, map_add, hφδ, hφδ]
    have hmem : preimageFun φ ∘ (d₁₂ B).hom (Function.surjInv hψ ∘ ((c : cocycles₁ C) : G → C)
        + Function.surjInv hψ ∘ ((c' : cocycles₁ C) : G → C)) ∈ levelCocycles₂ r A := by
      rw [e]; exact add_mem (mem c) (mem c')
    rw [← lift (c + c') _ hL hLc hmem]
    show continuousH2π r A ⟨_, hmem⟩ = continuousH2π r A ⟨_, mem c⟩ + continuousH2π r A ⟨_, mem c'⟩
    rw [← map_add]
    congr 1
    exact Subtype.ext e
  have hsmul : ∀ (t : k) (c : levelCocycles₁ r C), f (t • c) = t • f c := by
    intro t c
    have hL : IsLevelConstant₁ r (t • (Function.surjInv hψ ∘ ((c : cocycles₁ C) : G → C))) := (c.2.comp _).comp _
    have hLc : ∀ g, ψ.hom ((t • (Function.surjInv hψ ∘ ((c : cocycles₁ C) : G → C))) g)
        = (((t • c : levelCocycles₁ r C) : cocycles₁ C) : G → C) g := by
      intro g
      rw [Pi.smul_apply, map_smul, Function.comp_apply, hσ]
      rfl
    have e : preimageFun φ ∘ (d₁₂ B).hom (t • (Function.surjInv hψ ∘ ((c : cocycles₁ C) : G → C)))
        = t • deltaCochain₁ φ ψ hψ ((c : cocycles₁ C) : G → C) := by
      funext p
      apply hφ
      have lhs : φ.hom ((preimageFun φ ∘ (d₁₂ B).hom (t • (Function.surjInv hψ ∘ ((c : cocycles₁ C) : G → C)))) p)
          = t • (d₁₂ B).hom (Function.surjInv hψ ∘ ((c : cocycles₁ C) : G → C)) p := by
        rw [Function.comp_apply, map_smul, Pi.smul_apply]
        exact apply_preimageFun φ ⟨t • deltaCochain₁ φ ψ hψ ((c : cocycles₁ C) : G → C) p, by rw [map_smul, hφδ]⟩
      rw [lhs, Pi.smul_apply, map_smul, hφδ]
    have hmem : preimageFun φ ∘ (d₁₂ B).hom (t • (Function.surjInv hψ ∘ ((c : cocycles₁ C) : G → C)))
        ∈ levelCocycles₂ r A := by
      rw [e]; exact Submodule.smul_mem _ t (mem c)
    rw [← lift (t • c) _ hL hLc hmem]
    show continuousH2π r A ⟨_, hmem⟩ = t • continuousH2π r A ⟨_, mem c⟩
    rw [← map_smul]
    congr 1
    exact Subtype.ext e
  exact ⟨{ toFun := f, map_add' := hadd, map_smul' := hsmul }, fun c => ⟨mem c, rfl⟩⟩

end S_groupCohomology_exists_linearMap_levelCocycles1_continuousH2_eq_continuousH2pi_deltaCochain1
end P2MW
export P2MW.S_groupCohomology_exists_linearMap_levelCocycles1_continuousH2_eq_continuousH2pi_deltaCochain1 (solution)
