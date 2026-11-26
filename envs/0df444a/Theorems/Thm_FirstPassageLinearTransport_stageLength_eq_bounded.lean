-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_stageLength_eq_bounded
-- name    : FirstPassageLinearTransport.stageLength_eq_bounded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:04:46.541469+00:00
-- url     : https://prove2.me/theorems/d0973cb3-6be8-44fc-9fbf-23293c0bc5d3
-- title:
--   First Passage Linear Transport: stage Length eq bounded
-- statement:
--   The First Passage Linear Transport construction uses the stage Length eq bounded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Pullback.lean#L163-L167
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Pullback.lean#L163-L167

import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Definitions.Def_FirstPassageLinearTransport_Transport
import Definitions.Def_FirstPassageLinearTransport_Pullback
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.stageLength_eq_bounded {r eta : ℝ} (p : StageSetup r eta)
    {M n : ℕ} (hM : p.M0 ≤ M) (hnShell : n ∈ dyadicShell M) :
    stageLength p n = boundedFirstPassage (targetScale r M) M n := by sorry
