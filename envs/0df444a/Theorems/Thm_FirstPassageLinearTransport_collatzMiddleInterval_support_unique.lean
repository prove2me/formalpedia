-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_collatzMiddleInterval_support_unique
-- name    : FirstPassageLinearTransport.collatzMiddleInterval_support_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:32:43.671582+00:00
-- url     : https://prove2.me/theorems/5a362ecf-455a-5037-baec-1492523fb81e
-- title:
--   First Passage Linear Transport: collatz Middle Interval support unique
-- statement:
--   The First Passage Linear Transport construction uses the collatz Middle Interval support unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L1015-L1027
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L1015-L1027

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.collatzMiddleInterval_support_unique
    {r : ℕ} {a : ℝ} {v w : Fin r → Bool}
    (hv : collatzMiddleInterval a v)
    (hw : collatzMiddleInterval a w) :
    (boolSupport v).card = (boolSupport w).card := by sorry
