-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_eventuallyLogAddRpowLe
-- name    : FirstPassageLinearTransport.eventuallyLogAddRpowLe
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:28:47.63773+00:00
-- url     : https://prove2.me/theorems/d940a8e0-79ea-5850-9706-b64862ea4cde
-- title:
--   First Passage Linear Transport: eventually Log Add Rpow Le
-- statement:
--   A logarithmic startup term plus a strictly smaller power is eventually
--   dominated by the target power.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/StretchedLogLanding.lean#L24-L90
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/StretchedLogLanding.lean#L24-L90

import Definitions.Def_FirstPassageLinearTransport_BootstrapSchedule
import Definitions.Def_FirstPassageLinearTransport_StretchedLogLanding
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real Topology BigOperators
open Filter
noncomputable section

theorem FirstPassageLinearTransport.eventuallyLogAddRpowLe
    {A C c a delta : ℝ}
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hc : 0 < c)
    (hdelta : delta < 1) (ha : delta < a) :
    ∀ᶠ x : ℝ in atTop,
      A * Real.log x + C * x ^ (1 - a) ≤
        c * x ^ (1 - delta) := by sorry
