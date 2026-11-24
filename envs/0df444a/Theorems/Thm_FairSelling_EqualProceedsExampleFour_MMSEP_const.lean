-- Prove2me | Theorems.Thm_FairSelling_EqualProceedsExampleFour_MMSEP_const
-- name    : FairSelling.EqualProceedsExampleFour.MMSEP_const
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:50:26.717798+00:00
-- url     : https://prove2.me/theorems/3aa8c683-aba6-47b1-847b-a69ccd7e016e
-- title:
--   Equal Proceeds Example Four: MMSEP const
-- statement:
--   For a constant valuation `c` and unit prices, the equal-proceeds maximin share is
--   `max 1 c`: the agent either keeps one good per bundle, or sells everything and splits the
--   proceeds.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsExamples.lean#L264-L286
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsExamples.lean#L264-L286

import Mathlib
import Definitions.Def_RequestProject_EqualProceeds
import Definitions.Def_RequestProject_EqualProceedsExamples
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.EqualProceedsExampleFour
variable (N : ℕ)

theorem FairSelling.EqualProceedsExampleFour.MMSEP_const (c : ℝ) (hc : 0 ≤ c) :
    MMSEP (N + 2) (fun _ => c) (price N) = max 1 c := by sorry
