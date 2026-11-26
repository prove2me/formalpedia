-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_multiplicativeHitCount_succ_of_safe
-- name    : FirstPassageLinearTransport.multiplicativeHitCount_succ_of_safe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:36:47.104808+00:00
-- url     : https://prove2.me/theorems/0984bd80-9406-4089-8f1f-8f8e28ddef06
-- title:
--   First Passage Linear Transport: multiplicative Hit Count succ of safe
-- statement:
--   The First Passage Linear Transport construction uses the multiplicative Hit Count succ of safe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L2644-L2675
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L2644-L2675

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.multiplicativeHitCount_succ_of_safe
    {u z : ℝ} {r : ℕ} (hz : ¬u < z) :
    multiplicativeHitCount u (r + 1) z =
      multiplicativeHitCount u r (z * (3 / 2)) +
        multiplicativeHitCount u r (z * (1 / 2)) := by sorry
