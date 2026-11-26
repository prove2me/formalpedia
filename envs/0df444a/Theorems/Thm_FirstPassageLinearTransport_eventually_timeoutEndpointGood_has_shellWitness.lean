-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_eventually_timeoutEndpointGood_has_shellWitness
-- name    : FirstPassageLinearTransport.eventually_timeoutEndpointGood_has_shellWitness
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:50:55.44036+00:00
-- url     : https://prove2.me/theorems/420301cb-4654-489f-ab61-7c2c10b6ac97
-- title:
--   First Passage Linear Transport: eventually timeout Endpoint Good has shell Witness
-- statement:
--   Canonical timeout-good shell sources have one witness satisfying landing,
--   clock, and ceiling simultaneously.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutEndpointWitness.lean#L38-L193
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutEndpointWitness.lean#L38-L193

import Definitions.Def_FirstPassageLinearTransport_TimeoutTrajectoryProfile
import Definitions.Def_FirstPassageLinearTransport_PolylogTarget
import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointWitness
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.eventually_timeoutEndpointGood_has_shellWitness
    {Amax c beta : ℝ}
    (P : MovingEndpointParameterPackage Amax c beta)
    {A : ℕ → ℝ}
    (hbuffer : Tendsto (movingRankBuffer A) atTop atTop)
    (hUpper : ∀ᶠ M : ℕ in atTop, A M ≤ Amax) :
    ∀ᶠ M : ℕ in atTop, ∀ n : ℕ,
      n ∈ dyadicShell M →
      n ∈ timeoutEndpointGood P A M →
      ∃ k : ℕ,
        (k : ℝ) < c * (M : ℝ) * Real.log 2 ∧
        (orbit k n : ℝ) <
          fixedPolylogTargetConstant Amax * (Real.log n) ^ (A M) ∧
        ∀ j : ℕ, j ≤ k →
          (orbit j n : ℝ) ≤ (n : ℝ) ^ (1 + beta) := by sorry
