-- Prove2me | solution 1 for groupCohomology.nonempty_continuousH2_coind_linearEquiv_continuousH2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/a0597387-cb81-5466-912f-3d509dd4ae15

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_LevelSubgroup
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Theorems.Thm_groupCohomology_coind_mem_levelCoboundaries2_of_eval_one_mem_levelCoboundaries2
import Theorems.Thm_groupCohomology_exists_coind_mem_levelCocycles2_eval_one_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_nonempty_continuousH2_coind_linearEquiv_continuousH2

set_option autoImplicit false

universe u

open CategoryTheory

open groupCohomology in
theorem solution {k G : Type u} [CommRing k] [Group G]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (S : Subgroup G)
    (hS : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧ F₀.fixingSubgroup.comap r ≤ S)
    (N : Rep.{u} k S) :
    Nonempty (groupCohomology.continuousH2 r (Rep.coind S.subtype N)
      ≃ₗ[k] groupCohomology.continuousH2 (r.comp S.subtype) N) := by
  classical
  let evL : (Rep.coind S.subtype N) →ₗ[k] N :=
    { toFun := fun f => (f : G → N) 1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hev : ∀ (s : S) (f : Rep.coind S.subtype N),
      evL ((Rep.coind S.subtype N).ρ (S.subtype s) f) = N.ρ s (evL f) := fun s f => by
    show ((f : Rep.coind S.subtype N) : G → N) (1 * (s : G)) = N.ρ s (((f : Rep.coind S.subtype N) : G → N) 1)
    rw [one_mul, ← mul_one (s : G)]
    exact (f : Rep.coind S.subtype N).2 s 1
  have hf : ∀ s : S, r (S.subtype s) = (r.comp S.subtype) s := fun _ => rfl
  let Sh : continuousH2 r (Rep.coind S.subtype N) →ₗ[k] continuousH2 (r.comp S.subtype) N :=
    continuousH2Map S.subtype hf evL hev
  have coe_map : ∀ x : levelCocycles₂ r (Rep.coind S.subtype N),
      (levelCocycles₂Map S.subtype hf evL hev x : S × S → N)
        = fun p : S × S => ((x : G × G → Rep.coind S.subtype N) ((p.1 : G), (p.2 : G)) : G → N) 1 :=
    fun _ => rfl
  refine ⟨LinearEquiv.ofBijective Sh ⟨?_, ?_⟩⟩
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    induction z using Submodule.Quotient.induction_on with | _ x =>
    have h0 : Sh (continuousH2π r _ x) = 0 := hz
    have h1 : continuousH2π (r.comp S.subtype) N (levelCocycles₂Map S.subtype hf evL hev x) = 0 := h0
    rw [continuousH2π_eq_zero_iff, coe_map] at h1
    have := groupCohomology.coind_mem_levelCoboundaries2_of_eval_one_mem_levelCoboundaries2 r S hS N
      (x : G × G → Rep.coind S.subtype N) x.2 h1
    exact (continuousH2π_eq_zero_iff r _ x).2 this
  · intro y
    induction y using Submodule.Quotient.induction_on with | _ b =>
    obtain ⟨c, hc, hev'⟩ := groupCohomology.exists_coind_mem_levelCocycles2_eval_one_eq r S hS N
      (b : S × S → N) b.2
    refine ⟨continuousH2π r _ ⟨c, hc⟩, ?_⟩
    show continuousH2π (r.comp S.subtype) N (levelCocycles₂Map S.subtype hf evL hev ⟨c, hc⟩)
      = continuousH2π (r.comp S.subtype) N b
    congr 1
    apply Subtype.ext
    rw [coe_map]
    funext p
    exact hev' p.1 p.2

end S_groupCohomology_nonempty_continuousH2_coind_linearEquiv_continuousH2
end P2MW
export P2MW.S_groupCohomology_nonempty_continuousH2_coind_linearEquiv_continuousH2 (solution)
