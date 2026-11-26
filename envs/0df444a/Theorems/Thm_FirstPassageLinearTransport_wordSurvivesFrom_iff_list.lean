-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_wordSurvivesFrom_iff_list
-- name    : FirstPassageLinearTransport.wordSurvivesFrom_iff_list
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:33:35.475647+00:00
-- url     : https://prove2.me/theorems/937581a9-5a9a-4586-acce-011fd76a5ba8
-- title:
--   First Passage Linear Transport: word Survives From iff list
-- statement:
--   The First Passage Linear Transport construction uses the word Survives From iff list property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L1295-L1304
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L1295-L1304

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.wordSurvivesFrom_iff_list
    {r : ℕ} (lo : ℝ) (x : Bool → ℝ) (z : ℝ) (v : Fin r → Bool) :
    wordSurvivesFrom lo x r z v ↔
      listSurvivesFrom lo x z (List.ofFn v) := by sorry
