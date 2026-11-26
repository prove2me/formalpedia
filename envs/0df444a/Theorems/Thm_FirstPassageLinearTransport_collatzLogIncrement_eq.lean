-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_collatzLogIncrement_eq
-- name    : FirstPassageLinearTransport.collatzLogIncrement_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:32:35.323814+00:00
-- url     : https://prove2.me/theorems/0815709c-3628-5b26-800a-2ee1d05ffecb
-- title:
--   First Passage Linear Transport: collatz Log Increment eq
-- statement:
--   The First Passage Linear Transport construction uses the collatz Log Increment eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L933-L936
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L933-L936

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.collatzLogIncrement_eq (b : Bool) :
    collatzLogIncrement b =
      (if b then Real.log 3 else 0) - Real.log 2 := by sorry
