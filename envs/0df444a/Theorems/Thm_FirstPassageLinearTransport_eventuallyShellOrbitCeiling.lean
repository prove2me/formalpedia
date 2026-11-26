-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_eventuallyShellOrbitCeiling
-- name    : FirstPassageLinearTransport.eventuallyShellOrbitCeiling
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:45:58.842697+00:00
-- url     : https://prove2.me/theorems/1ff0ccb0-482b-4851-97f3-85811e28d1fe
-- title:
--   First Passage Linear Transport: eventually Shell Orbit Ceiling
-- statement:
--   On the logarithmic stage schedule, the fixed startup factor in the
--   all-prefix envelope is swallowed by every strict exponent margin
--   `eta < beta`.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/OrbitCeiling.lean#L500-L586
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/OrbitCeiling.lean#L500-L586

import Definitions.Def_FirstPassageLinearTransport_NaturalDensityDescent
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
import Definitions.Def_FirstPassageLinearTransport_RawDynamics
import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.eventuallyShellOrbitCeiling
    {r eta omega beta : ℝ} (p : StageSetup r eta)
    (homega : 0 < omega) (hetaBeta : eta < beta) :
    ∀ᶠ M : ℕ in atTop, ∀ n : ℕ,
      0 < n → n ∈ dyadicShell M →
      n ∈ bootstrapSet p (stageCount omega M) →
      ∀ j : ℕ, j ≤ stageClock p (stageCount omega M) n →
        (orbit j n : ℝ) ≤ (n : ℝ) ^ (1 + beta) := by sorry
