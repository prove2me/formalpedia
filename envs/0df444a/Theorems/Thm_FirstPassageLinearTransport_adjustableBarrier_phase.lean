-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_adjustableBarrier_phase
-- name    : FirstPassageLinearTransport.adjustableBarrier_phase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:13:11.120603+00:00
-- url     : https://prove2.me/theorems/175ef917-2bf6-48c8-9e6d-75685f31fb73
-- title:
--   First Passage Linear Transport: adjustable Barrier phase
-- statement:
--   The multiplicative phase inequality for the adjustable height.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/AdjustableEnvelope.lean#L79-L99
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/AdjustableEnvelope.lean#L79-L99

import Definitions.Def_FirstPassageLinearTransport_EntropyBarrier
import Definitions.Def_FirstPassageLinearTransport_Envelope
import Definitions.Def_FirstPassageLinearTransport_AdjustableEnvelope
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.adjustableBarrier_phase
    {lambda t : ℝ} {M n : ℕ}
    (hlambda1 : lambda ≤ 1)
    (ht : 0 ≤ t) (hnShell : n ∈ dyadicShell M) :
    (3 : ℝ) ^ adjustableBarrierHeight lambda t M ≤ (n : ℝ) ^ t := by sorry
