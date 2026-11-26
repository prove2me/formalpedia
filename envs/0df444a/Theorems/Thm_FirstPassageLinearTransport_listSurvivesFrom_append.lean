-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_listSurvivesFrom_append
-- name    : FirstPassageLinearTransport.listSurvivesFrom_append
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:29:33.277733+00:00
-- url     : https://prove2.me/theorems/39aaf992-3896-41d6-9d7b-1784cbfbd339
-- title:
--   First Passage Linear Transport: list Survives From append
-- statement:
--   The First Passage Linear Transport construction uses the list Survives From append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L1237-L1262
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L1237-L1262

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.listSurvivesFrom_append (lo : ℝ) (x : Bool → ℝ)
    (z : ℝ) (l r : List Bool) :
    listSurvivesFrom lo x z (l ++ r) ↔
      listSurvivesFrom lo x z l ∧
        listSurvivesFrom lo x (z + listIncrementSum x l) r := by sorry
