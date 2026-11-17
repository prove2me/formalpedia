-- Prove2me | solution 1 for lowerSum_le_taggedSum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:13:03.351413+00:00
-- url     : https://prove2.me/submissions/e0a83cb9-3d00-4aeb-aed3-7bf76e44ab0c

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Mathlib.Tactic
import Theorems.Thm_DarbouxRS_lowerSum_le_taggedSum
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped BigOperators Pointwise Interval
noncomputable section

theorem solution {a b : ℝ} {f alpha : ℝ → ℝ}
    (hs : SourceHypotheses a b f alpha)
    (P : Partition a b)
    (tags : Fin P.n → ℝ)
    (htags : tagsInPartition P tags) :
    lowerSum P f alpha ≤ taggedSum P tags f alpha :=
  DarbouxRS.lowerSum_le_taggedSum hs P tags htags
