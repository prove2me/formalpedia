-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_rawOddDeviationCoefficient_nonneg
-- name    : FirstPassageLinearTransport.rawOddDeviationCoefficient_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:28:24.372576+00:00
-- url     : https://prove2.me/theorems/00311ad8-b7cb-4416-8fe3-ecf6dc15a4ef
-- title:
--   First Passage Linear Transport: raw Odd Deviation Coefficient nonneg
-- statement:
--   The First Passage Linear Transport construction uses the raw Odd Deviation Coefficient nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L40-L45
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L40-L45

import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
import Definitions.Def_FirstPassageLinearTransport_TimeoutTrajectoryProfile
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.rawOddDeviationCoefficient_nonneg :
    0 ≤ rawOddDeviationCoefficient := by sorry
