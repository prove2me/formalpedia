-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_card_shellMaximalParityBad_adjustable_le
-- name    : FirstPassageLinearTransport.card_shellMaximalParityBad_adjustable_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:14:28.992114+00:00
-- url     : https://prove2.me/theorems/4af01cd7-cb96-4e09-8639-0dee92ddfab9
-- title:
--   First Passage Linear Transport: card shell Maximal Parity Bad adjustable le
-- statement:
--   Entropy-sharp count for the adjustable maximal-parity exceptional set.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/AdjustableBarrierDensity.lean#L121-L134
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/AdjustableBarrierDensity.lean#L121-L134

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_FirstPassageLinearTransport_AdjustableEnvelope
import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Definitions.Def_FirstPassageLinearTransport_AdjustableBarrierDensity
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.card_shellMaximalParityBad_adjustable_le
    {lambda t : ℝ} (M : ℕ)
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    (ht0 : 0 ≤ t) (htA : t < a0) :
    ((shellMaximalParityBad M
      (adjustableBarrierHeight lambda t M)).card : ℝ) ≤
      (2 : ℝ) ^ (M + 1) *
        Real.exp (-((M : ℝ) *
          binaryBarrierRate (adjustableBarrierDisplacement lambda t))) := by sorry
