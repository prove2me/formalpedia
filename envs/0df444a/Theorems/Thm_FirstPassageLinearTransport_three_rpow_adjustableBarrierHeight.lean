-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_three_rpow_adjustableBarrierHeight
-- name    : FirstPassageLinearTransport.three_rpow_adjustableBarrierHeight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:02:14.285902+00:00
-- url     : https://prove2.me/theorems/d7830b81-fe50-4595-bf5a-368b0fe23610
-- title:
--   First Passage Linear Transport: three rpow adjustable Barrier Height
-- statement:
--   The First Passage Linear Transport construction uses the three rpow adjustable Barrier Height property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/AdjustableEnvelope.lean#L29-L37
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/AdjustableEnvelope.lean#L29-L37

import Definitions.Def_FirstPassageLinearTransport_EntropyBarrier
import Definitions.Def_FirstPassageLinearTransport_Envelope
import Definitions.Def_FirstPassageLinearTransport_AdjustableEnvelope
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.three_rpow_adjustableBarrierHeight
    (lambda t : ℝ) (M : ℕ) :
    (3 : ℝ) ^ adjustableBarrierHeight lambda t M =
      (2 : ℝ) ^ (lambda * t * (M : ℝ)) := by sorry
