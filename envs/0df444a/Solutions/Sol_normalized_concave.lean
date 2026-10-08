-- Prove2me | solution 1 for normalized_concave
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T15:21:48.867527+00:00
-- url     : https://prove2.me/submissions/ff812d66-1f15-4151-ac5d-6a77f887f21d

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem solution
    (g : ℝ → ℝ) (c : ℝ) (hconc : ConcaveOn ℝ (Set.Ici 0) g) :
    ConcaveOn ℝ (Set.Ici 0) (fun t => g t - c * t) := by
  refine ⟨hconc.1, ?_⟩
  intro x hx y hy u v hu hv huv
  have h := hconc.2 hx hy hu hv huv
  dsimp at h ⊢
  nlinarith [h]
