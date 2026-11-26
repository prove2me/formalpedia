-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_parityDigitR_nonneg
-- name    : FirstPassageLinearTransport.parityDigitR_nonneg
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:03:56.892719+00:00
-- url     : https://prove2.me/theorems/25e9df97-d354-55a4-b2d9-521cd6127b76
-- title:
--   First Passage Linear Transport: parity Digit R nonneg
-- statement:
--   The First Passage Linear Transport construction uses the parity Digit R nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Envelope.lean#L77-L79
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Envelope.lean#L77-L79

import Mathlib.Algebra.Ring.GeomSum
import Definitions.Def_FirstPassageLinearTransport_Barrier
import Definitions.Def_FirstPassageLinearTransport_Envelope
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real BigOperators
noncomputable section

theorem FirstPassageLinearTransport.parityDigitR_nonneg (n i : ℕ) : 0 ≤ parityDigitR n i := by sorry
