-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_scale
-- name    : FirstPassageLinearTransport.ballotWordValue_scale
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:28:01.016773+00:00
-- url     : https://prove2.me/theorems/851dd904-4566-4364-be02-2b8c2a8fa196
-- title:
--   First Passage Linear Transport: ballot Word Value scale
-- statement:
--   The First Passage Linear Transport construction uses the ballot Word Value scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L3012-L3015
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L3012-L3015

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.ballotWordValue_scale
    {r : ℕ} (z : ℝ) (v : Fin r → Bool) :
    ballotWordValue z v = z * ballotWordValue 1 v := by sorry
