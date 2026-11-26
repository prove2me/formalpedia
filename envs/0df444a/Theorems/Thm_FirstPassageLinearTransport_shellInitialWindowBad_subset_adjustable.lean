-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_shellInitialWindowBad_subset_adjustable
-- name    : FirstPassageLinearTransport.shellInitialWindowBad_subset_adjustable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:14:22.638507+00:00
-- url     : https://prove2.me/theorems/fd99da75-efcb-4a7b-a679-de0835434631
-- title:
--   First Passage Linear Transport: shell Initial Window Bad subset adjustable
-- statement:
--   A failure of the central orbit envelope is contained in the adjustable
--   maximal-parity exceptional set once the two explicit startups hold.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/AdjustableBarrierDensity.lean#L98-L118
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/AdjustableBarrierDensity.lean#L98-L118

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_FirstPassageLinearTransport_AdjustableEnvelope
import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Definitions.Def_FirstPassageLinearTransport_AdjustableBarrierDensity
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.shellInitialWindowBad_subset_adjustable
    {lambda t : ℝ} {M : ℕ}
    (hlambda1 : lambda ≤ 1) (ht : 0 ≤ t)
    (hmainStartup : 1 ≤ (1 - lambda) * t * (M : ℝ))
    (hcorrectionStartup :
      2 * (2 + Real.sqrt 3) ≤
        (2 : ℝ) ^ ((a0 + t - 2 * lambda * t) * (M : ℝ))) :
    shellInitialWindowBad M t ⊆
      shellMaximalParityBad M (adjustableBarrierHeight lambda t M) := by sorry
