-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_eventuallyShellRawClockLt
-- name    : FirstPassageLinearTransport.eventuallyShellRawClockLt
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:22:08.81035+00:00
-- url     : https://prove2.me/theorems/e2ee4e71-b0bc-5799-b988-8ea8c3736df0
-- title:
--   First Passage Linear Transport: eventually Shell Raw Clock Lt
-- statement:
--   Uniform shellwise raw clock below any strict budget exceeding the leading
--   coefficient.  The logarithmic-stage error is swallowed by `log n`.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/RawClockBudget.lean#L230-L377
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/RawClockBudget.lean#L230-L377

import Definitions.Def_FirstPassageLinearTransport_RawDynamics
import Definitions.Def_FirstPassageLinearTransport_ClockBudget
import Definitions.Def_FirstPassageLinearTransport_RawClockBudget
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.eventuallyShellRawClockLt
    {r eta omega rawClock : ℝ} (p : StageSetup r eta)
    (homega0 : 0 < omega)
    (hleading : rawClockLeading r eta < rawClock) :
    ∀ᶠ M : ℕ in atTop, ∀ n : ℕ,
      0 < n → n ∈ dyadicShell M →
      n ∈ bootstrapSet p (stageCount omega M) →
      (rawTime n (stageClock p (stageCount omega M) n) : ℝ) <
        rawClock * Real.log n := by sorry
