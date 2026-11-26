-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_card_shellInitialWindowBad_adjustable_le
-- name    : FirstPassageLinearTransport.card_shellInitialWindowBad_adjustable_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:14:51.430805+00:00
-- url     : https://prove2.me/theorems/527fe677-fe81-43fd-bb58-6829f03ed06f
-- title:
--   First Passage Linear Transport: card shell Initial Window Bad adjustable le
-- statement:
--   The actual orbit-envelope failures obey the entropy-sharp shell count
--   whenever the two finite-startup inequalities hold.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/AdjustableBarrierDensity.lean#L138-L163
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/AdjustableBarrierDensity.lean#L138-L163

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_FirstPassageLinearTransport_AdjustableEnvelope
import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Definitions.Def_FirstPassageLinearTransport_AdjustableBarrierDensity
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.card_shellInitialWindowBad_adjustable_le
    {lambda t : ℝ} {M : ℕ}
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    (ht0 : 0 ≤ t) (htA : t < a0)
    (hmainStartup : 1 ≤ (1 - lambda) * t * (M : ℝ))
    (hcorrectionStartup :
      2 * (2 + Real.sqrt 3) ≤
        (2 : ℝ) ^ ((a0 + t - 2 * lambda * t) * (M : ℝ))) :
    ((shellInitialWindowBad M t).card : ℝ) ≤
      (2 : ℝ) ^ (M + 1) *
        Real.exp (-((M : ℝ) *
          binaryBarrierRate (adjustableBarrierDisplacement lambda t))) := by sorry
