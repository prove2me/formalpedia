-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_tendsto_movingLowLambda
-- name    : FirstPassageLinearTransport.tendsto_movingLowLambda
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:24:33.78394+00:00
-- url     : https://prove2.me/theorems/cc556099-ddde-4c65-ab22-d1b60b1339f6
-- title:
--   First Passage Linear Transport: tendsto moving Low Lambda
-- statement:
--   The First Passage Linear Transport construction uses the tendsto moving Low Lambda property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/MovingLowParameters.lean#L139-L144
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/MovingLowParameters.lean#L139-L144

import Mathlib.Analysis.Calculus.MeanValue
import Definitions.Def_FirstPassageLinearTransport_FixedPolylogParameters
import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Definitions.Def_FirstPassageLinearTransport_MovingLowParameters
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.tendsto_movingLowLambda (K₁ : ℝ) :
    Tendsto (movingLowLambda K₁) atTop (nhds 1) := by sorry
