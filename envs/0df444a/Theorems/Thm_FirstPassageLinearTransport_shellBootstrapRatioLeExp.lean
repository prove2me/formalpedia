-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_shellBootstrapRatioLeExp
-- name    : FirstPassageLinearTransport.shellBootstrapRatioLeExp
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:28:17.331795+00:00
-- url     : https://prove2.me/theorems/541c9018-546e-5eb3-a8ba-33910fcf7367
-- title:
--   First Passage Linear Transport: shell Bootstrap Ratio Le Exp
-- statement:
--   Before taking the logarithmic stage schedule, the shell error has this
--   single exact exponential majorant.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/BootstrapSchedule.lean#L53-L90
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/BootstrapSchedule.lean#L53-L90

import Definitions.Def_FirstPassageLinearTransport_GlobalAssembly
import Definitions.Def_FirstPassageLinearTransport_BootstrapSchedule
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real Topology BigOperators
open Filter
noncomputable section

theorem FirstPassageLinearTransport.shellBootstrapRatioLeExp
    {r eta chi Dc : ℝ} (p : StageSetup r eta)
    (hchi0 : 0 < chi) (hchir : chi < r) (hchi1 : chi ≤ 1)
    (hDc0 : 0 < Dc) (hDc1 : Dc ≤ 1)
    (hDcRate : Dc ≤ quadraticWindowDensityRate eta)
    (hchiDc : chi * Dc < 1) (R M : ℕ) :
    shellExceptionalRatio (bootstrapSet p R) M ≤
      Real.exp (Real.log 2 + bootstrapLogBound p chi Dc R -
        Real.log 2 * bootstrapD chi Dc R * M) := by sorry
