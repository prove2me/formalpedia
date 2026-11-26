-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_three_rpow_adjustableBarrierHeight_sq
-- name    : FirstPassageLinearTransport.three_rpow_adjustableBarrierHeight_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:13:00.69894+00:00
-- url     : https://prove2.me/theorems/c58dddf3-af6c-46c9-8f96-fc61bc072ec7
-- title:
--   First Passage Linear Transport: three rpow adjustable Barrier Height sq
-- statement:
--   The square of the affine-correction barrier has the exact exponent used by
--   the startup comparison.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/AdjustableEnvelope.lean#L41-L48
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/AdjustableEnvelope.lean#L41-L48

import Definitions.Def_FirstPassageLinearTransport_EntropyBarrier
import Definitions.Def_FirstPassageLinearTransport_Envelope
import Definitions.Def_FirstPassageLinearTransport_AdjustableEnvelope
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.three_rpow_adjustableBarrierHeight_sq
    (lambda t : ℝ) (M : ℕ) :
    (3 : ℝ) ^ adjustableBarrierHeight lambda t M *
        (3 : ℝ) ^ adjustableBarrierHeight lambda t M =
      (2 : ℝ) ^ (2 * lambda * t * (M : ℝ)) := by sorry
