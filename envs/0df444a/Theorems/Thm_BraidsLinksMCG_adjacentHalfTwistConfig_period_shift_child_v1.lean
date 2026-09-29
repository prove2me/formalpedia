-- Prove2me | Theorems.Thm_BraidsLinksMCG_adjacentHalfTwistConfig_period_shift_child_v1
-- name    : BraidsLinksMCG.adjacentHalfTwistConfig_period_shift_child_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-23T21:47:20.597796+00:00
-- url     : https://prove2.me/theorems/64adcca8-0fd5-47e8-bae6-1a4029f97809
-- title:
--   A half-twist period shifts time by swapping the active pair
-- statement:
--   Advancing the adjacent half-twist parameter by one full turn leaves every inactive strand fixed and interchanges the two active strands. This equivariance is the path identity used to compare a two-period full twist with the concatenation of half-twist loops.
-- source:
--   Exact source lemma adjacentHalfTwistConfig_period_shift from the preserved proof route for BraidsLinksMCG.standardGen_image_last_eq_last_halfTwist_square_v1 (target a5d61856-8526-4cf8-960c-b185fcf7fd81). It is used pointwise in the double-twist path comparison.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_BraidsLinksMCG_ArtinEndo
import Definitions.Def_TarchaBraids_HalfTwist
open BraidsLinksMCG TarchaBraids

theorem BraidsLinksMCG.adjacentHalfTwistConfig_period_shift_child_v1 (n : ℕ) (u : ℝ) :
    (TarchaBraids.halfTwistConfig (n + 2) (Fin.last n) u).1 =
      (TarchaBraids.halfTwistConfig (n + 2) (Fin.last n) (u + 1)).1 ∘
        Equiv.swap (BraidsLinksMCG.strandIdx (Fin.last n))
          (BraidsLinksMCG.strandIdxSucc (Fin.last n)) := by sorry
