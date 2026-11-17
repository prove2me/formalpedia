-- Prove2me | solution 1 for rsTaggedCommonLimit_of_rsUpperLowerCommonLimit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:13:19.263405+00:00
-- url     : https://prove2.me/submissions/ead668ed-7e1d-4ea9-a7ba-d775f8cbe56c

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Mathlib.Tactic
import Theorems.Thm_DarbouxRS_lowerSum_le_taggedSum
import Theorems.Thm_DarbouxRS_taggedSum_le_upperSum
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped BigOperators Pointwise Interval
noncomputable section

theorem solution
    {a b : ℝ} {f alpha : ℝ → ℝ} {L : ℝ}
    (h : rsUpperLowerCommonLimit a b f alpha L) :
    rsTaggedCommonLimit a b f alpha L := by
  -- Unfold the exported aliases.
  unfold rsUpperLowerCommonLimit at h
  unfold rsTaggedCommonLimit

  rcases h with ⟨hs, hlim⟩

  refine ⟨hs, ?_⟩

  intro eps heps

  rcases hlim eps heps with ⟨δ, hδ, Hδ⟩

  refine ⟨δ, hδ, ?_⟩

  intro P tags htags hmesh

  have hP :
      |upperSum P f alpha - L| < eps ∧
      |lowerSum P f alpha - L| < eps :=
    Hδ P hmesh

  have h_lower :
      lowerSum P f alpha ≤ taggedSum P tags f alpha :=
    DarbouxRS.lowerSum_le_taggedSum hs P tags htags

  have h_upper :
      taggedSum P tags f alpha ≤ upperSum P f alpha :=
    DarbouxRS.taggedSum_le_upperSum hs P tags htags

  have h_upper_abs :
      |upperSum P f alpha - L| < eps :=
    hP.1

  have h_lower_abs :
      |lowerSum P f alpha - L| < eps :=
    hP.2

  apply abs_lt.mpr
  constructor
  · -- lower side: `-eps < taggedSum P tags f alpha - L`
    have h_lower_left :
        -eps < lowerSum P f alpha - L :=
      (abs_lt.mp h_lower_abs).1
    linarith

  · -- upper side: `taggedSum P tags f alpha - L < eps`
    have h_upper_right :
        upperSum P f alpha - L < eps :=
      (abs_lt.mp h_upper_abs).2
    linarith
