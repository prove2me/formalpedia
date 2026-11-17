-- Prove2me | solution 1 for taggedSum_le_upperSum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:13:10.956635+00:00
-- url     : https://prove2.me/submissions/4ff143be-ab73-44e4-8858-540e34c1f027

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Mathlib.Tactic
import Theorems.Thm_DarbouxRS_taggedSum_le_upperSum
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
    taggedSum P tags f alpha ≤ upperSum P f alpha :=
  DarbouxRS.taggedSum_le_upperSum hs P tags htags
