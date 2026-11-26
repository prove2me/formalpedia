-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_tendsto_movingShellError_zero
-- name    : FirstPassageLinearTransport.tendsto_movingShellError_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:37:52.451088+00:00
-- url     : https://prove2.me/theorems/afda33e0-6920-4593-a0d5-e768ead1a6f5
-- title:
--   First Passage Linear Transport: tendsto moving Shell Error zero
-- statement:
--   The two terms in the shell bound vanish when the critical buffer tends to
--   infinity and the high-rank exponent is positive.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/MovingEndpointScalars.lean#L494-L515
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/MovingEndpointScalars.lean#L494-L515

import Definitions.Def_FirstPassageLinearTransport_ShrinkingParameters
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
import Definitions.Def_FirstPassageLinearTransport_MovingEndpointScalars
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.tendsto_movingShellError_zero
    {A : ℕ → ℝ} {eps : ℝ}
    (hbuffer : Tendsto (movingRankBuffer A) atTop atTop)
    (heps : 0 < eps) :
    Tendsto
      (fun M : ℕ =>
        (2 : ℝ) ^ (-(movingRankBuffer A M)) +
          (((M : ℝ) + 2) ^ (-eps)))
      atTop (nhds 0) := by sorry
