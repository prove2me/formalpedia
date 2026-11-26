-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_eventually_card_shellInitialWindowBad_adjustable_le
-- name    : FirstPassageLinearTransport.eventually_card_shellInitialWindowBad_adjustable_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:14:42.376069+00:00
-- url     : https://prove2.me/theorems/e2367397-f6a3-470d-93f7-e5bf4eab8e5d
-- title:
--   First Passage Linear Transport: eventually card shell Initial Window Bad adjustable le
-- statement:
--   Eventual entropy-sharp shell count, with no startup hypotheses left in the
--   consumer.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/AdjustableBarrierDensity.lean#L167-L178
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/AdjustableBarrierDensity.lean#L167-L178

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_FirstPassageLinearTransport_AdjustableEnvelope
import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Definitions.Def_FirstPassageLinearTransport_AdjustableBarrierDensity
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.eventually_card_shellInitialWindowBad_adjustable_le
    {lambda t : ℝ} (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda < 1)
    (ht0 : 0 < t) (htA : t < a0) :
    ∀ᶠ M : ℕ in atTop,
      ((shellInitialWindowBad M t).card : ℝ) ≤
        (2 : ℝ) ^ (M + 1) *
          Real.exp (-((M : ℝ) *
            binaryBarrierRate (adjustableBarrierDisplacement lambda t))) := by sorry
