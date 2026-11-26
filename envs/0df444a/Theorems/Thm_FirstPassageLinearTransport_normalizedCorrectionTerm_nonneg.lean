-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_normalizedCorrectionTerm_nonneg
-- name    : FirstPassageLinearTransport.normalizedCorrectionTerm_nonneg
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:04:07.083796+00:00
-- url     : https://prove2.me/theorems/8e1153cf-b3ba-5ae4-b8ff-b6605970e258
-- title:
--   First Passage Linear Transport: normalized Correction Term nonneg
-- statement:
--   The First Passage Linear Transport construction uses the normalized Correction Term nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Envelope.lean#L94-L97
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Envelope.lean#L94-L97

import Mathlib.Algebra.Ring.GeomSum
import Definitions.Def_FirstPassageLinearTransport_Barrier
import Definitions.Def_FirstPassageLinearTransport_Envelope
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real BigOperators
noncomputable section

theorem FirstPassageLinearTransport.normalizedCorrectionTerm_nonneg (k n i : ℕ) :
    0 ≤ normalizedCorrectionTerm k n i := by sorry
