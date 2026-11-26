-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_eventually_adjustableBarrier_startups
-- name    : FirstPassageLinearTransport.eventually_adjustableBarrier_startups
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:14:28.971307+00:00
-- url     : https://prove2.me/theorems/2efd40b6-f8f3-491f-a410-6cfbf4a3148f
-- title:
--   First Passage Linear Transport: eventually adjustable Barrier startups
-- statement:
--   Both startup inequalities for the adjustable envelope hold at every
--   sufficiently large shell rank.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/AdjustableBarrierDensity.lean#L53-L94
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/AdjustableBarrierDensity.lean#L53-L94

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_FirstPassageLinearTransport_AdjustableEnvelope
import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Definitions.Def_FirstPassageLinearTransport_AdjustableBarrierDensity
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.eventually_adjustableBarrier_startups
    {lambda t : ℝ} (hlambda1 : lambda < 1)
    (ht0 : 0 < t) (htA : t < a0) :
    ∀ᶠ M : ℕ in atTop,
      1 ≤ (1 - lambda) * t * (M : ℝ) ∧
        2 * (2 + Real.sqrt 3) ≤
          (2 : ℝ) ^ ((a0 + t - 2 * lambda * t) * (M : ℝ)) := by sorry
