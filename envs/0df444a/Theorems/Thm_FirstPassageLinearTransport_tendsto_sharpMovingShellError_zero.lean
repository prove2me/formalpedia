-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_tendsto_sharpMovingShellError_zero
-- name    : FirstPassageLinearTransport.tendsto_sharpMovingShellError_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:37:55.047801+00:00
-- url     : https://prove2.me/theorems/a2cf7235-e370-5700-90da-92746726b6c5
-- title:
--   First Passage Linear Transport: tendsto sharp Moving Shell Error zero
-- statement:
--   The two terms in the sharp Version 4 shell profile vanish when the new
--   critical buffer diverges.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/MovingEndpointScalars.lean#L519-L542
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/MovingEndpointScalars.lean#L519-L542

import Definitions.Def_FirstPassageLinearTransport_ShrinkingParameters
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
import Definitions.Def_FirstPassageLinearTransport_MovingEndpointScalars
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.tendsto_sharpMovingShellError_zero
    {A : ℕ → ℝ} {eps : ℝ}
    (hbuffer : Tendsto (sharpMovingRankBuffer A) atTop atTop)
    (heps : 0 < eps) :
    Tendsto
      (fun M : ℕ =>
        (2 : ℝ) ^ (-(sharpMovingRankBuffer A M)) +
          (((M : ℝ) + 2) ^ (-eps)))
      atTop (nhds 0) := by sorry
