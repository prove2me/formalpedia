-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_scaledReverseLoss_le_half_time
-- name    : FirstPassageLinearTransport.scaledReverseLoss_le_half_time
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:05:25.236257+00:00
-- url     : https://prove2.me/theorems/432f8e36-030c-47f7-b648-6f663ef0aa25
-- title:
--   First Passage Linear Transport: scaled Reverse Loss le half time
-- statement:
--   A first-passage block of length `h` has scaled reverse loss at most
--   `h / 2` at its own threshold.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/NestedRecertification.lean#L82-L106
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/NestedRecertification.lean#L82-L106

import Definitions.Def_FirstPassageLinearTransport_LossTransport
import Definitions.Def_FirstPassageLinearTransport_RawDynamics
import Definitions.Def_FirstPassageLinearTransport_NestedRecertification
set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section

theorem FirstPassageLinearTransport.scaledReverseLoss_le_half_time
    {Y n h : ℕ} (hY : 0 < Y) (hfp : IsFirstPassage Y n h) :
    scaledReverseLoss Y n h ≤ (h : ℚ) / 2 := by sorry
