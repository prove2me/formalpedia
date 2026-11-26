-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_log_ballotWordValue_one
-- name    : FirstPassageLinearTransport.log_ballotWordValue_one
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:37:33.431424+00:00
-- url     : https://prove2.me/theorems/e87b97a0-3c9c-4a13-a116-bc468147ff52
-- title:
--   First Passage Linear Transport: log ballot Word Value one
-- statement:
--   The First Passage Linear Transport construction uses the log ballot Word Value one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L3185-L3191
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L3185-L3191

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.log_ballotWordValue_one
    {r : ℕ} (v : Fin r → Bool) :
    Real.log (ballotWordValue 1 v) =
      ((boolSupport v).card : ℝ) * Real.log 3 -
        (r : ℝ) * Real.log 2 := by sorry
