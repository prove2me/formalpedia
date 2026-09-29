-- Prove2me | solution 1 for groupCohomology.deltaCochain0_mem_coboundaries1_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/402166ad-9396-5d3c-819e-f3d96ccb5187

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Definitions.Def_GroupCohomology_ContinuousH1
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_deltaCochain0_mem_coboundaries1_iff

set_option autoImplicit false

universe u

open CategoryTheory

namespace P2mS26U6
open groupCohomology

variable {k G : Type u} [CommRing k] [Group G]
  {r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)} {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C)

theorem isLevelConstant₁_d₀₁ {m : B}
    (hm : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s, r s ∈ F.fixingSubgroup → B.ρ s m = m) :
    IsLevelConstant₁ r ((d₀₁ B).hom m) := by
  obtain ⟨F, hF, h⟩ := hm
  refine ⟨F, hF, fun g s hs => ?_⟩
  rw [d₀₁_hom_apply, d₀₁_hom_apply, map_mul, Module.End.mul_apply, h s hs]

end P2mS26U6

open P2mS26U6 groupCohomology in
theorem solution {k G : Type u} [CommRing k] [Group G] {A B C : Rep.{u} k G} (φ : A ⟶ B) (ψ : B ⟶ C)
    (hφ : Function.Injective φ.hom) (hψ : Function.Surjective ψ.hom) (hex : ∀ b : B, ψ.hom b = 0 ↔ ∃ a : A, φ.hom a = b)
    (c : C) (hc : c ∈ C.ρ.invariants) :
    groupCohomology.deltaCochain₀ φ ψ hψ c ∈ groupCohomology.coboundaries₁ A ↔
      ∃ b ∈ B.ρ.invariants, ψ.hom b = c := by
  have hσc : ψ.hom (Function.surjInv hψ c) = c := Function.surjInv_eq hψ c
  have hker : ∀ g, ψ.hom (B.ρ g (Function.surjInv hψ c) - Function.surjInv hψ c) = 0 := fun g => by
    rw [map_sub, Rep.hom_comm_apply, hσc, sub_eq_zero]; exact hc g
  have hφδ : ∀ g, φ.hom (deltaCochain₀ φ ψ hψ c g) = B.ρ g (Function.surjInv hψ c) - Function.surjInv hψ c :=
    fun g => by rw [deltaCochain₀_apply]; exact apply_preimageFun φ ((hex _).1 (hker g))
  constructor
  · rintro ⟨a₀, ha₀⟩
    refine ⟨Function.surjInv hψ c - φ.hom a₀, fun g => ?_, ?_⟩
    · have h1 := congrFun ha₀ g
      rw [d₀₁_hom_apply] at h1
      have h2 := hφδ g
      rw [← h1, map_sub, Rep.hom_comm_apply] at h2
      rw [map_sub]
      calc B.ρ g (Function.surjInv hψ c) - B.ρ g (φ.hom a₀)
          = (B.ρ g (Function.surjInv hψ c) - Function.surjInv hψ c) - (B.ρ g (φ.hom a₀) - φ.hom a₀)
              + (Function.surjInv hψ c - φ.hom a₀) := by abel
        _ = Function.surjInv hψ c - φ.hom a₀ := by rw [h2, sub_self, zero_add]
    · rw [map_sub, hσc, (hex _).2 ⟨a₀, rfl⟩, sub_zero]
  · rintro ⟨b, hb, hbc⟩
    obtain ⟨a₀, ha₀⟩ := (hex (Function.surjInv hψ c - b)).1 (by rw [map_sub, hσc, hbc, sub_self])
    refine ⟨a₀, funext fun g => hφ ?_⟩
    rw [d₀₁_hom_apply, map_sub, Rep.hom_comm_apply, ha₀, hφδ, map_sub, hb g]
    abel

end S_groupCohomology_deltaCochain0_mem_coboundaries1_iff
end P2MW
export P2MW.S_groupCohomology_deltaCochain0_mem_coboundaries1_iff (solution)
