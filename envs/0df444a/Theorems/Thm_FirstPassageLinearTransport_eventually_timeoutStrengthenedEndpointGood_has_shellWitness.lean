-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_eventually_timeoutStrengthenedEndpointGood_has_shellWitness
-- name    : FirstPassageLinearTransport.eventually_timeoutStrengthenedEndpointGood_has_shellWitness
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:50:43.866283+00:00
-- url     : https://prove2.me/theorems/5c11f83f-49b7-5684-b595-c2772b232323
-- title:
--   First Passage Linear Transport: eventually timeout Strengthened Endpoint Good has shell Witness
-- statement:
--   Strengthened shell witness: the landing is shared by the shortcut and raw
--   maps, and both trajectories obey the prescribed shellwise relative-height
--   allowance.  The shortcut proof retains a factor-two reserve used by the raw
--   interleaving.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutEndpointWitness.lean#L199-L502
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutEndpointWitness.lean#L199-L502

import Definitions.Def_FirstPassageLinearTransport_TimeoutTrajectoryProfile
import Definitions.Def_FirstPassageLinearTransport_PolylogTarget
import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointWitness
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.eventually_timeoutStrengthenedEndpointGood_has_shellWitness
    {Amax c beta : ℝ}
    (P : MovingEndpointParameterPackage Amax c beta)
    {A R : ℕ → ℝ}
    (hbuffer : Tendsto (sharpMovingRankBuffer A) atTop atTop)
    (hUpper : ∀ᶠ M : ℕ in atTop, A M ≤ Amax)
    (hR : ∀ᶠ M : ℕ in atTop, 4 ≤ R M) :
    ∀ᶠ M : ℕ in atTop, ∀ n : ℕ,
      n ∈ dyadicShell M →
      n ∈ timeoutStrengthenedEndpointGood P A R M →
      ∃ k ell : ℕ,
        (k : ℝ) < c * (M : ℝ) * Real.log 2 ∧
        |driftGap * (k : ℝ) - (M : ℝ)| ≤
          2 * timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch *
            Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) ∧
        |(2 * driftGap / 3) * (ell : ℝ) - (M : ℝ)| ≤
          timeoutCompletedRawClockSupportConstant P.run.toTimeoutHigh P.Cswitch *
            Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) ∧
        (∀ j : ℕ, j ≤ k →
          |shortcutLogDeviation n j| ≤
            2 * timeoutTimeSupportConstant P.run.toTimeoutHigh P.Cswitch *
              Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2))) ∧
        (∀ j : ℕ, j ≤ k →
          |(oddCount n j : ℝ) - (j : ℝ) / 2| ≤
            timeoutCompletedOddTrajectorySupportConstant
                P.run.toTimeoutHigh P.Cswitch *
              Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2))) ∧
        (∀ i : ℕ, i ≤ ell →
          |rawLogDeviation n i| ≤
            timeoutCompletedRawTrajectorySupportConstant
                P.run.toTimeoutHigh P.Cswitch *
              Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2))) ∧
        ell = rawTime n k ∧
        rawOrbit ell n = orbit k n ∧
        (orbit k n : ℝ) <
          fixedPolylogTargetConstant Amax * (Real.log n) ^ (A M) ∧
        (∀ j : ℕ, j ≤ k →
          (orbit j n : ℝ) ≤ (n : ℝ) * R M / 2) ∧
        (∀ i : ℕ, i ≤ ell →
          (rawOrbit i n : ℝ) ≤ (n : ℝ) * R M) := by sorry
