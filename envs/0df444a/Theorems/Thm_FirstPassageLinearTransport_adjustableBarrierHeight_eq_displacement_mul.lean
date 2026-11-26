-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_adjustableBarrierHeight_eq_displacement_mul
-- name    : FirstPassageLinearTransport.adjustableBarrierHeight_eq_displacement_mul
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:13:47.611737+00:00
-- url     : https://prove2.me/theorems/ce349b66-6b9e-44ef-9119-e020fd2871c5
-- title:
--   First Passage Linear Transport: adjustable Barrier Height eq displacement mul
-- statement:
--   The First Passage Linear Transport construction uses the adjustable Barrier Height eq displacement mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/AdjustableBarrierDensity.lean#L29-L34
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/AdjustableBarrierDensity.lean#L29-L34

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_FirstPassageLinearTransport_AdjustableEnvelope
import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Definitions.Def_FirstPassageLinearTransport_AdjustableBarrierDensity
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.adjustableBarrierHeight_eq_displacement_mul
    (lambda t : ℝ) (M : ℕ) :
    adjustableBarrierHeight lambda t M =
      adjustableBarrierDisplacement lambda t * (M : ℝ) := by sorry
