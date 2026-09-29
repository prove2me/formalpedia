-- Prove2me | solution 1 for groupCohomology.exists_div_mem_of_isMulCocycle1_of_presentation
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/4557c6d2-2180-5870-9acb-a45dfcd61e67

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_exists_div_mem_of_isMulCocycle1_of_presentation

set_option autoImplicit false
open groupCohomology

set_option maxHeartbeats 1600000 in
theorem solution
    {G M P : Type*} [Group G] [CommGroup M] [MulDistribMulAction G M] [AddCommGroup P] [SMul G P]
    (Fn Fn1 : Subgroup M) (hstab : ∀ (g : G) (x : M), x ∈ Fn → g • x ∈ Fn)
    (π : M → P) (hπmul : ∀ x y, x ∈ Fn → y ∈ Fn → π (x * y) = π x + π y)
    (hπsurj : ∀ p : P, ∃ x ∈ Fn, π x = p)
    (hπker : ∀ x, x ∈ Fn → (π x = 0 ↔ x ∈ Fn1))
    (hπsmul : ∀ (g : G) (x : M), x ∈ Fn → π (g • x) = g • π x)
    (hP : ∀ f : G → P, IsCocycle₁ f → IsCoboundary₁ f)
    (f : G → M) (hfF : ∀ g, f g ∈ Fn) (hf : IsMulCocycle₁ f) :
    ∃ a ∈ Fn, ∀ g, f g / (g • a / a) ∈ Fn1 := by
  have hπdiv : ∀ x y, x ∈ Fn → y ∈ Fn → π (x / y) = π x - π y := by
    intro x y hx hy
    have h := hπmul (x / y) y (Fn.div_mem hx hy) hy
    rw [div_mul_cancel] at h
    exact eq_sub_of_add_eq h.symm
  have hc : IsCocycle₁ (fun g => π (f g)) := by
    intro g h
    simp only
    rw [hf g h, hπmul _ _ (hstab _ _ (hfF h)) (hfF g), hπsmul _ _ (hfF h)]
  obtain ⟨x, hx⟩ := hP _ hc
  obtain ⟨a, haF, rfl⟩ := hπsurj x
  refine ⟨a, haF, fun g => ?_⟩
  have hga : g • a ∈ Fn := hstab g a haF
  rw [← hπker _ (Fn.div_mem (hfF g) (Fn.div_mem hga haF)), hπdiv _ _ (hfF g) (Fn.div_mem hga haF),
    hπdiv _ _ hga haF, hπsmul _ _ haF, hx g, sub_self]

end S_groupCohomology_exists_div_mem_of_isMulCocycle1_of_presentation
end P2MW
export P2MW.S_groupCohomology_exists_div_mem_of_isMulCocycle1_of_presentation (solution)
