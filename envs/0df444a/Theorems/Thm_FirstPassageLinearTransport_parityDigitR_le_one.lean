-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_parityDigitR_le_one
-- name    : FirstPassageLinearTransport.parityDigitR_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:04:03.0478+00:00
-- url     : https://prove2.me/theorems/f307ca36-6976-5e89-a2ef-4ad04c8d8e5d
-- title:
--   First Passage Linear Transport: parity Digit R le one
-- statement:
--   The First Passage Linear Transport construction uses the parity Digit R le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Envelope.lean#L81-L83
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Envelope.lean#L81-L83

import Mathlib.Algebra.Ring.GeomSum
import Definitions.Def_FirstPassageLinearTransport_Barrier
import Definitions.Def_FirstPassageLinearTransport_Envelope
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real BigOperators
noncomputable section

theorem FirstPassageLinearTransport.parityDigitR_le_one (n i : ℕ) : parityDigitR n i ≤ 1 := by sorry
