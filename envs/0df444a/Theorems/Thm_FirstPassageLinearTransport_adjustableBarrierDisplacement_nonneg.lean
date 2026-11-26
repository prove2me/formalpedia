-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_adjustableBarrierDisplacement_nonneg
-- name    : FirstPassageLinearTransport.adjustableBarrierDisplacement_nonneg
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:13:50.180852+00:00
-- url     : https://prove2.me/theorems/10ac9043-28ce-4b48-80ba-b4cdc807e225
-- title:
--   First Passage Linear Transport: adjustable Barrier Displacement nonneg
-- statement:
--   The First Passage Linear Transport construction uses the adjustable Barrier Displacement nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/AdjustableBarrierDensity.lean#L36-L39
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/AdjustableBarrierDensity.lean#L36-L39

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_FirstPassageLinearTransport_AdjustableEnvelope
import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Definitions.Def_FirstPassageLinearTransport_AdjustableBarrierDensity
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.adjustableBarrierDisplacement_nonneg
    {lambda t : ℝ} (hlambda : 0 ≤ lambda) (ht : 0 ≤ t) :
    0 ≤ adjustableBarrierDisplacement lambda t := by sorry
