-- Prove2me | solution 1 for groupCohomology.comp_mem_coboundaries1_iff_exists_invariants_sub_deltaCochain0
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/0dac543d-3262-51ad-a551-5236d3dcd586

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Definitions.Def_GroupCohomology_ContinuousH1
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_comp_mem_coboundaries1_iff_exists_invariants_sub_deltaCochain0

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
    (a : groupCohomology.cocycles₁ A) :
    (φ.hom ∘ a) ∈ groupCohomology.coboundaries₁ B ↔
      ∃ c ∈ C.ρ.invariants, ((a : G → A) - groupCohomology.deltaCochain₀ φ ψ hψ c) ∈ groupCohomology.coboundaries₁ A := by
  have hσ : ∀ x : C, ψ.hom (Function.surjInv hψ x) = x := Function.surjInv_eq hψ
  constructor
  · rintro ⟨b, hb⟩

    have hb' : ∀ g, φ.hom (a g) = B.ρ g b - b := fun g => by
      have := congrFun hb g; rw [d₀₁_hom_apply] at this; exact this.symm
    have hc : ψ.hom b ∈ C.ρ.invariants := fun g => by
      rw [← Rep.hom_comm_apply, ← sub_eq_zero, ← map_sub, ← hb', (hex _).2 ⟨a g, rfl⟩]
    refine ⟨ψ.hom b, hc, ?_⟩

    obtain ⟨a₁, ha₁⟩ := (hex (Function.surjInv hψ (ψ.hom b) - b)).1 (by rw [map_sub, hσ, sub_self])
    have hker : ∀ g, ψ.hom (B.ρ g (Function.surjInv hψ (ψ.hom b)) - Function.surjInv hψ (ψ.hom b)) = 0 :=
      fun g => by rw [map_sub, Rep.hom_comm_apply, hσ, sub_eq_zero]; exact hc g
    have hφδ : ∀ g, φ.hom (deltaCochain₀ φ ψ hψ (ψ.hom b) g)
        = B.ρ g (Function.surjInv hψ (ψ.hom b)) - Function.surjInv hψ (ψ.hom b) :=
      fun g => by rw [deltaCochain₀_apply]; exact apply_preimageFun φ ((hex _).1 (hker g))
    refine ⟨-a₁, funext fun g => hφ ?_⟩
    have e1 : φ.hom (((a : G → A) - deltaCochain₀ φ ψ hψ (ψ.hom b)) g)
        = (B.ρ g b - b) - (B.ρ g (Function.surjInv hψ (ψ.hom b)) - Function.surjInv hψ (ψ.hom b)) := by
      rw [Pi.sub_apply, map_sub, hb', hφδ]
    have e2 : φ.hom ((d₀₁ A).hom (-a₁) g) = -(B.ρ g (φ.hom a₁) - φ.hom a₁) := by
      simp only [d₀₁_hom_apply, map_sub, map_neg, Rep.hom_comm_apply]; abel
    rw [e2, e1, ha₁, map_sub]
    abel
  · rintro ⟨c, hc, a₁, ha₁⟩
    have hker : ∀ g, ψ.hom (B.ρ g (Function.surjInv hψ c) - Function.surjInv hψ c) = 0 :=
      fun g => by rw [map_sub, Rep.hom_comm_apply, hσ, sub_eq_zero]; exact hc g
    have hφδ : ∀ g, φ.hom (deltaCochain₀ φ ψ hψ c g) = B.ρ g (Function.surjInv hψ c) - Function.surjInv hψ c :=
      fun g => by rw [deltaCochain₀_apply]; exact apply_preimageFun φ ((hex _).1 (hker g))

    refine ⟨Function.surjInv hψ c + φ.hom a₁, funext fun g => ?_⟩
    have h1 := congrFun ha₁ g
    rw [d₀₁_hom_apply, Pi.sub_apply] at h1
    rw [d₀₁_hom_apply, Function.comp_apply, map_add, ← Rep.hom_comm_apply,
      show (a : G → A) g = deltaCochain₀ φ ψ hψ c g + (A.ρ g a₁ - a₁) by rw [h1]; abel,
      map_add, hφδ, map_sub]
    abel

end S_groupCohomology_comp_mem_coboundaries1_iff_exists_invariants_sub_deltaCochain0
end P2MW
export P2MW.S_groupCohomology_comp_mem_coboundaries1_iff_exists_invariants_sub_deltaCochain0 (solution)
