-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_adjustableBarrier_phase_two
-- name    : FirstPassageLinearTransport.adjustableBarrier_phase_two
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:13:20.897539+00:00
-- url     : https://prove2.me/theorems/d4e6a683-365d-4c48-9bf0-26fbee7ea12d
-- title:
--   First Passage Linear Transport: adjustable Barrier phase two
-- statement:
--   Once the unused multiplicative exponent is at least one bit, the factor
--   two needed by the upper main term is also absorbed.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/AdjustableEnvelope.lean#L103-L133
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/AdjustableEnvelope.lean#L103-L133

import Definitions.Def_FirstPassageLinearTransport_EntropyBarrier
import Definitions.Def_FirstPassageLinearTransport_Envelope
import Definitions.Def_FirstPassageLinearTransport_AdjustableEnvelope
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.adjustableBarrier_phase_two
    {lambda t : ℝ} {M n : ℕ}
    (ht : 0 ≤ t)
    (hstartup : 1 ≤ (1 - lambda) * t * (M : ℝ))
    (hnShell : n ∈ dyadicShell M) :
    2 * (3 : ℝ) ^ adjustableBarrierHeight lambda t M ≤ (n : ℝ) ^ t := by sorry
