-- Prove2me | solution 1 for endpoint_secants_of_inSubdiff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T17:26:17.446982+00:00
-- url     : https://prove2.me/submissions/23c70f36-465b-413a-ba5f-53c16660019a

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem solution
    (g : ℝ → ℝ) (a c : ℝ) (ha : 0 ≤ a)
    (hconc : ConcaveOn ℝ (Set.Ici 0) g) (hsub : InSubdiff g a c) :
    (∀ x, x ∈ Set.Icc 0 a → x < a → c ≤ slope g x a) ∧
      (∀ y, a < y → slope g a y ≤ c) := by
  rcases hsub with ⟨⟨r, hright, hrc⟩, hleft⟩
  have hconcR : ConcaveOn ℝ (Set.Ici a) g := by
    refine ⟨convex_Ici a, ?_⟩
    intro x hx y hy u v hu hv huv
    exact hconc.2
      (Set.mem_Ici.mpr (le_trans ha (Set.mem_Ici.mp hx)))
      (Set.mem_Ici.mpr (le_trans ha (Set.mem_Ici.mp hy))) hu hv huv
  constructor
  · intro x hx hxa
    rcases hleft with ha0 | ⟨l, hleft_deriv, hcl⟩
    · rw [ha0] at hxa
      have hx_eq_zero : x = 0 := by
        rcases hx with ⟨hxlo, hxa'⟩
        linarith
      linarith
    · have hconcL : ConcaveOn ℝ (Set.Icc 0 a) g := by
        refine ⟨convex_Icc 0 a, ?_⟩
        intro z hz w hw u v hu hv huv
        exact hconc.2
          (Set.mem_Ici.mpr hz.1) (Set.mem_Ici.mpr hw.1) hu hv huv
      have hleft' : HasDerivWithinAt g l (Set.Icc 0 a) a :=
        hleft_deriv.mono (by
          intro z hz
          exact hz.2)
      have ha' : a ∈ Set.Icc 0 a := ⟨ha, le_rfl⟩
      exact le_trans hcl
        (ConcaveOn.le_slope_of_hasDerivWithinAt hconcL hx ha' hxa hleft')
  · intro y hay
    exact le_trans
      (ConcaveOn.slope_le_of_hasDerivWithinAt hconcR
        (Set.mem_Ici.mpr le_rfl)
        (le_of_lt hay) hay hright)
      hrc
