-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_centralOrbitScale_eq_two_rpow_neg_gap
-- name    : FirstPassageLinearTransport.centralOrbitScale_eq_two_rpow_neg_gap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:04:21.587174+00:00
-- url     : https://prove2.me/theorems/6e9adb61-c3a2-418c-8564-0f27388c61df
-- title:
--   First Passage Linear Transport: central Orbit Scale eq two rpow neg gap
-- statement:
--   The First Passage Linear Transport construction uses the central Orbit Scale eq two rpow neg gap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Envelope.lean#L313-L320
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Envelope.lean#L313-L320

import Mathlib.Algebra.Ring.GeomSum
import Definitions.Def_FirstPassageLinearTransport_Barrier
import Definitions.Def_FirstPassageLinearTransport_Envelope
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real BigOperators
noncomputable section

theorem FirstPassageLinearTransport.centralOrbitScale_eq_two_rpow_neg_gap (k : ℕ) :
    centralOrbitScale k = (2 : ℝ) ^ (-driftGap * k) := by sorry
