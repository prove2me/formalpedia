-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_extendedWindow_powerDense
-- name    : FirstPassageLinearTransport.extendedWindow_powerDense
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:04:28.810187+00:00
-- url     : https://prove2.me/theorems/d658f68a-7bca-4b6a-a8ab-37006ad869b4
-- title:
--   First Passage Linear Transport: extended Window power Dense
-- statement:
--   Adding the finite startup window preserves the quantitative density of
--   the initial barrier-good set.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Pullback.lean#L111-L117
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Pullback.lean#L111-L117

import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Definitions.Def_FirstPassageLinearTransport_Transport
import Definitions.Def_FirstPassageLinearTransport_Pullback
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.extendedWindow_powerDense {r eta : ℝ}
    (p : StageSetup r eta) :
    PowerDense (extendedWindow p)
      (quadraticWindowGlobalConstant eta)
      (quadraticWindowDensityRate eta) := by sorry
