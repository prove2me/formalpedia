-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_eventuallyShellBootstrapRatioLeStretched
-- name    : FirstPassageLinearTransport.eventuallyShellBootstrapRatioLeStretched
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:44:35.355496+00:00
-- url     : https://prove2.me/theorems/f1e1aae7-e4f3-5e8c-8674-20f19192976d
-- title:
--   First Passage Linear Transport: eventually Shell Bootstrap Ratio Le Stretched
-- statement:
--   Quantitative strengthening of the varying-shell estimate.  Every strict
--   power below the density exponent is available with shell prefactor `2`.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/BootstrapSchedule.lean#L324-L446
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/BootstrapSchedule.lean#L324-L446

import Definitions.Def_FirstPassageLinearTransport_GlobalAssembly
import Definitions.Def_FirstPassageLinearTransport_BootstrapSchedule
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real Topology BigOperators
open Filter
noncomputable section
set_option maxHeartbeats 2000000

theorem FirstPassageLinearTransport.eventuallyShellBootstrapRatioLeStretched
    {r eta chi Dc omega sigma : ℝ} (p : StageSetup r eta)
    (hchi0 : 0 < chi) (hchir : chi < r) (hchi1 : chi ≤ 1)
    (hDc0 : 0 < Dc) (hDc1 : Dc ≤ 1)
    (hDcRate : Dc ≤ quadraticWindowDensityRate eta)
    (hchiDc : chi * Dc < 1)
    (homega0 : 0 < omega)
    (hsigma0 : 0 < sigma)
    (hsigma : sigma < 1 - densityGamma omega chi) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ M : ℕ in atTop,
      shellExceptionalRatio (shellBootstrap p omega M) M ≤
        2 * Real.exp (-c * ((M : ℝ) + 4) ^ sigma) := by sorry
