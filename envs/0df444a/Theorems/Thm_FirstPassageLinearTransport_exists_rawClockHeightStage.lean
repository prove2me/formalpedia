-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_exists_rawClockHeightStage
-- name    : FirstPassageLinearTransport.exists_rawClockHeightStage
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:57:30.58727+00:00
-- url     : https://prove2.me/theorems/5353e499-ece5-5d22-b866-1ba36ea5aa8d
-- title:
--   First Passage Linear Transport: exists raw Clock Height Stage
-- statement:
--   Shrink the raw-clock envelope width once more so that all later
--   fixed-barrier blocks lie below the original source scale.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/StretchedRelativeHeight.lean#L627-L667
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/StretchedRelativeHeight.lean#L627-L667

import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_RawNaturalDensityDescent
import Definitions.Def_FirstPassageLinearTransport_StretchedExceptionalCount
import Definitions.Def_FirstPassageLinearTransport_StretchedRelativeHeight
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.exists_rawClockHeightStage
    {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta < 1) :
    ∃ (h : HeadlineScalars delta) (eta : ℝ) (_p : StageSetup h.r eta),
      eta < h.r - a0 ∧
      rawClockLeading h.r eta < (261 / 25 : ℝ) ∧
      h.r * (1 + eta) < 1 := by sorry
