-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_timeoutEndpointNaturalDensityDescent
-- name    : FirstPassageLinearTransport.timeoutEndpointNaturalDensityDescent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:51:06.334963+00:00
-- url     : https://prove2.me/theorems/d1798c7f-be53-431b-9137-eae00e5d0332
-- title:
--   First Passage Linear Transport: timeout Endpoint Natural Density Descent
-- statement:
--   Complete timeout-endpoint theorem, retaining its literal shell error.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutEndpointNaturalDensity.lean#L37-L108
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutEndpointNaturalDensity.lean#L37-L108

import Definitions.Def_FirstPassageLinearTransport_MovingEndpointAssembly
import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointAsymptotics
import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointWitness
import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointNaturalDensity
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.timeoutEndpointNaturalDensityDescent
    {A : ℕ → ℝ} {Amax c beta : ℝ}
    (hAmax : 0 < Amax)
    (hc : fixedPolylogClockCritical < c)
    (hbeta : 0 < beta)
    (hbuffer : Tendsto (movingRankBuffer A) atTop atTop)
    (hUpper : ∀ᶠ M : ℕ in atTop, A M ≤ Amax) :
    ∃ S : Set ℕ, ∃ C eps : ℝ,
      0 < C ∧ 0 < eps ∧ NaturalDensityOne S ∧
      (∀ᶠ M : ℕ in atTop,
        shellExceptionalRatio S M ≤
          C * ((2 : ℝ) ^ (-(movingRankBuffer A M)) +
            (((M : ℝ) + 2) ^ (-eps)))) ∧
      (∀ᶠ n : ℕ in atTop, n ∈ S →
        ∃ k : ℕ,
          (k : ℝ) < c * Real.log n ∧
          (orbit k n : ℝ) <
            C * (Real.log n) ^ (A (Nat.log 2 n)) ∧
          ∀ j : ℕ, j ≤ k →
            (orbit j n : ℝ) ≤ (n : ℝ) ^ (1 + beta)) := by sorry
