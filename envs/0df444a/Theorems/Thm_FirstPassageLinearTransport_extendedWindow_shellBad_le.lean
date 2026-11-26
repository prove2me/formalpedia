-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_extendedWindow_shellBad_le
-- name    : FirstPassageLinearTransport.extendedWindow_shellBad_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:09:41.302922+00:00
-- url     : https://prove2.me/theorems/9cdcc8eb-ad56-44f4-8549-9b7963fac7bd
-- title:
--   First Passage Linear Transport: extended Window shell Bad le
-- statement:
--   The fixed maximal-barrier complement is cheaper than the requested
--   `chi*D` shell exponent whenever `chi*D ≤ D_eta`.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Pullback.lean#L445-L497
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Pullback.lean#L445-L497

import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Definitions.Def_FirstPassageLinearTransport_Transport
import Definitions.Def_FirstPassageLinearTransport_Pullback
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.extendedWindow_shellBad_le
    {r eta D chi Dc : ℝ} (p : StageSetup r eta)
    (hDDc : D ≤ Dc)
    (hchi0 : 0 ≤ chi)
    (hDcRate : chi * Dc ≤ quadraticWindowDensityRate eta)
    (M : ℕ) :
    ((shellBad (extendedWindow p) M).card : ℝ) ≤
      2 * quadraticWindowGlobalConstant eta *
        Real.exp (-(chi * D * Real.log 2 * M)) * (2 : ℝ) ^ M := by sorry
