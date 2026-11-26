-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_tendsto_movingLowCorrectionGap
-- name    : FirstPassageLinearTransport.tendsto_movingLowCorrectionGap
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:38:20.256222+00:00
-- url     : https://prove2.me/theorems/4262f048-dd55-4aa2-a38b-22551042f6a7
-- title:
--   First Passage Linear Transport: tendsto moving Low Correction Gap
-- statement:
--   The additive-correction exponent has the strictly positive endpoint
--   limit `2*a₀-1`.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/MovingLowParameters.lean#L148-L167
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/MovingLowParameters.lean#L148-L167

import Mathlib.Analysis.Calculus.MeanValue
import Definitions.Def_FirstPassageLinearTransport_FixedPolylogParameters
import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Definitions.Def_FirstPassageLinearTransport_MovingLowParameters
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.tendsto_movingLowCorrectionGap (K₀ K₁ : ℝ) :
    Tendsto
      (fun L : ℕ =>
        a0 + movingLowTolerance K₀ L -
          2 * movingLowLambda K₁ L * movingLowTolerance K₀ L)
      atTop (nhds (2 * a0 - 1)) := by sorry
