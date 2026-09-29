-- Prove2me | solution 1 for groupCohomology.exists_cocycles1_unramified_iff_mem_inflationImage_sup
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/a67cf388-64a7-5490-af0d-c6a03e6642cf

import Mathlib
import Definitions.Def_GroupCohomology_LocallyConstantClasses
import Theorems.Thm_groupCohomology_mem_inflationImage_iff_exists_cocycles1_apply_eq_zero
import Theorems.Thm_groupCohomology_cocycles1_apply_eq_zero_of_mem_closure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_exists_cocycles1_unramified_iff_mem_inflationImage_sup

open CategoryTheory Module groupCohomology

universe u

theorem solution {k G : Type u} [CommRing k] [Group G] (M : Rep k G) (I U : Subgroup G) [I.Normal] [U.Normal]
    (hU : ∀ u ∈ U, M.ρ u = 1) (x : H1 M) :
    (∃ c : cocycles₁ M, H1π M c = x ∧ (∀ u ∈ U, c u = 0) ∧
        ∃ m : M, ∀ g ∈ I, c g = M.ρ g m - m)
      ↔ x ∈ inflationImage M (I ⊔ U) := by
  constructor
  · rintro ⟨c, rfl, hcU, m, hcI⟩

    let b : cocycles₁ M := ⟨(d₀₁ M).hom m, coboundaries₁_le_cocycles₁ M (LinearMap.mem_range_self _ m)⟩
    have hb : ∀ g : G, b g = M.ρ g m - m := fun g => d₀₁_hom_apply M m g
    have hclass : H1π M (c - b) = H1π M c := by
      rw [map_sub, sub_eq_self]
      exact (H1π_eq_zero_iff b).2 (LinearMap.mem_range_self _ m)
    rw [groupCohomology.mem_inflationImage_iff_exists_cocycles1_apply_eq_zero]
    refine ⟨c - b, hclass, fun n hn => ?_⟩
    refine groupCohomology.cocycles1_apply_eq_zero_of_mem_closure (c - b) (s := (I : Set G) ∪ U) ?_ ?_
    · rintro g (hg | hg)
      · show c g - b g = 0
        rw [hb, hcI g hg, sub_self]
      · show c g - b g = 0
        rw [hb, hcU g hg, hU g hg, Module.End.one_apply, sub_self, sub_zero]
    · rwa [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
  · intro hx
    obtain ⟨c, rfl, hc⟩ :=
      (groupCohomology.mem_inflationImage_iff_exists_cocycles1_apply_eq_zero M (I ⊔ U) _).1 hx
    exact ⟨c, rfl, fun u hu => hc u (Subgroup.mem_sup_right hu),
      0, fun g hg => by rw [hc g (Subgroup.mem_sup_left hg), map_zero, sub_zero]⟩

end S_groupCohomology_exists_cocycles1_unramified_iff_mem_inflationImage_sup
end P2MW
export P2MW.S_groupCohomology_exists_cocycles1_unramified_iff_mem_inflationImage_sup (solution)
