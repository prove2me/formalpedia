-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_normalizedCorrection_nonneg
-- name    : FirstPassageLinearTransport.normalizedCorrection_nonneg
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:01:08.455388+00:00
-- url     : https://prove2.me/theorems/e32414bb-0013-42f6-96e6-e8e3f6a7e1f9
-- title:
--   First Passage Linear Transport: normalized Correction nonneg
-- statement:
--   The First Passage Linear Transport construction uses the normalized Correction nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Envelope.lean#L99-L101
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Envelope.lean#L99-L101

import Mathlib.Algebra.Ring.GeomSum
import Definitions.Def_FirstPassageLinearTransport_Barrier
import Definitions.Def_FirstPassageLinearTransport_Envelope
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real BigOperators
noncomputable section

theorem FirstPassageLinearTransport.normalizedCorrection_nonneg (k n : ℕ) :
    0 ≤ normalizedCorrection k n := by sorry
