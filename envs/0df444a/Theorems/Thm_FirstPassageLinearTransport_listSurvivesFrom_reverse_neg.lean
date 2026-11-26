-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_listSurvivesFrom_reverse_neg
-- name    : FirstPassageLinearTransport.listSurvivesFrom_reverse_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:33:41.534903+00:00
-- url     : https://prove2.me/theorems/6c4993d9-599b-5e4b-8d5d-e4bf6b9348a4
-- title:
--   First Passage Linear Transport: list Survives From reverse neg
-- statement:
--   If a word remains above `lo` and ends below `hi`, its reversed-negated
--   word remains above `lo-hi`.  This is the deterministic source of the second
--   outer-block survival condition.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L1267-L1293
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L1267-L1293

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.listSurvivesFrom_reverse_neg
    {lo hi z : ℝ} {x : Bool → ℝ} {l : List Bool}
    (hs : listSurvivesFrom lo x z l)
    (ht : z + listIncrementSum x l < hi) :
    listSurvivesFrom (lo - hi) (fun b => -x b) 0 l.reverse := by sorry
