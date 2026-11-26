-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_durationError_low_le
-- name    : FirstPassageLinearTransport.durationError_low_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:18:35.129339+00:00
-- url     : https://prove2.me/theorems/f6a9fe17-d2f3-4e4c-b326-c4ec32abbbd1
-- title:
--   First Passage Linear Transport: duration Error low le
-- statement:
--   The fixed low-rank width is at most a linear rank cost.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingTimeSupport.lean#L115-L120
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingTimeSupport.lean#L115-L120

import Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierRun
import Definitions.Def_FirstPassageLinearTransport_ShrinkingTimeSupport
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.durationError_low_le
    (P : ShrinkingBarrierRunData) {m : ℕ} (hm : 1 ≤ m) :
    durationError P.etaLo m ≤ (2 * P.etaLo + 3) * (m : ℝ) := by sorry
