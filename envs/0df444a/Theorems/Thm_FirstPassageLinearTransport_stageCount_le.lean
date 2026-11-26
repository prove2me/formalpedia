-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_stageCount_le
-- name    : FirstPassageLinearTransport.stageCount_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:14:11.07644+00:00
-- url     : https://prove2.me/theorems/250a98cb-f691-4156-b5ff-83b9abe353f8
-- title:
--   First Passage Linear Transport: stage Count le
-- statement:
--   The First Passage Linear Transport construction uses the stage Count le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Scalar.lean#L71-L78
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Scalar.lean#L71-L78

import Definitions.Def_FirstPassageLinearTransport_Bootstrap
import Definitions.Def_FirstPassageLinearTransport_Scalar
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real Topology BigOperators
open Filter Asymptotics
noncomputable section

theorem FirstPassageLinearTransport.stageCount_le {omega : ℝ} (homega : 0 ≤ omega) (M : ℕ) :
    (stageCount omega M : ℝ) ≤ omega * Real.log (M + 4) := by sorry
