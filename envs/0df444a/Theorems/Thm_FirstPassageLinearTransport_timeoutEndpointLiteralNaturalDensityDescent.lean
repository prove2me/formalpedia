-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_timeoutEndpointLiteralNaturalDensityDescent
-- name    : FirstPassageLinearTransport.timeoutEndpointLiteralNaturalDensityDescent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:27:15.207325+00:00
-- url     : https://prove2.me/theorems/f0dea8d5-b9f7-530c-917f-32b0abb22bda
-- title:
--   First Passage Linear Transport: timeout Endpoint Literal Natural Density Descent
-- statement:
--   Referee-facing timeout form: the shell exceptional set is literally the
--   set of sources without a simultaneous landing/clock/ceiling witness.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutEndpointNaturalDensity.lean#L112-L173
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutEndpointNaturalDensity.lean#L112-L173

import Definitions.Def_FirstPassageLinearTransport_MovingEndpointAssembly
import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointAsymptotics
import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointWitness
import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointNaturalDensity
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.timeoutEndpointLiteralNaturalDensityDescent
    {A : ℕ → ℝ} {Amax c beta : ℝ}
    (hAmax : 0 < Amax)
    (hc : fixedPolylogClockCritical < c)
    (hbeta : 0 < beta)
    (hbuffer : Tendsto (movingRankBuffer A) atTop atTop)
    (hUpper : ∀ᶠ M : ℕ in atTop, A M ≤ Amax) :
    ∃ C eps : ℝ,
      0 < C ∧ 0 < eps ∧
      NaturalDensityOne
        (assembleDyadic (timeoutEndpointWitnessGood A c beta C)) ∧
      (∀ᶠ M : ℕ in atTop,
        shellExceptionalRatio
            (timeoutEndpointWitnessGood A c beta C M) M ≤
          C * ((2 : ℝ) ^ (-(movingRankBuffer A M)) +
            (((M : ℝ) + 2) ^ (-eps)))) ∧
      (∀ n : ℕ,
        n ∈ assembleDyadic (timeoutEndpointWitnessGood A c beta C) →
          ∃ k : ℕ,
            (k : ℝ) < c * Real.log n ∧
            (orbit k n : ℝ) <
              C * (Real.log n) ^ (A (Nat.log 2 n)) ∧
            ∀ j : ℕ, j ≤ k →
              (orbit j n : ℝ) ≤ (n : ℝ) ^ (1 + beta)) := by sorry
