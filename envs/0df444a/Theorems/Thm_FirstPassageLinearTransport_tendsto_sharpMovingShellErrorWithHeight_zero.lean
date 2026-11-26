-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_tendsto_sharpMovingShellErrorWithHeight_zero
-- name    : FirstPassageLinearTransport.tendsto_sharpMovingShellErrorWithHeight_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:37:57.960245+00:00
-- url     : https://prove2.me/theorems/e09b11ca-4689-5264-874c-575b631b2e63
-- title:
--   First Passage Linear Transport: tendsto sharp Moving Shell Error With Height zero
-- statement:
--   The complete Version 4 shell error, including the reciprocal relative-
--   height allowance, tends to zero.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/MovingEndpointScalars.lean#L546-L564
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/MovingEndpointScalars.lean#L546-L564

import Definitions.Def_FirstPassageLinearTransport_ShrinkingParameters
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
import Definitions.Def_FirstPassageLinearTransport_MovingEndpointScalars
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.tendsto_sharpMovingShellErrorWithHeight_zero
    {A R : ℕ → ℝ} {C eps : ℝ}
    (hbuffer : Tendsto (sharpMovingRankBuffer A) atTop atTop)
    (heps : 0 < eps) (hR : Tendsto R atTop atTop) :
    Tendsto
      (fun M : ℕ =>
        C * ((2 : ℝ) ^ (-(sharpMovingRankBuffer A M)) +
          (((M : ℝ) + 2) ^ (-eps))) + 4 / R M)
      atTop (nhds 0) := by sorry
