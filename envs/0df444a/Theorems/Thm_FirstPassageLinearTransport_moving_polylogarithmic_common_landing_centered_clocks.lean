-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_moving_polylogarithmic_common_landing_centered_clocks
-- name    : FirstPassageLinearTransport.moving_polylogarithmic_common_landing_centered_clocks
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:53:41.052187+00:00
-- url     : https://prove2.me/theorems/ac6202d4-5246-5101-b468-8e580d194221
-- title:
--   First Passage Linear Transport: moving polylogarithmic common landing centered clocks
-- statement:
--   Sharp moving-endpoint conclusion with an independently prescribed
--   polynomial shell error and relative-height allowance.  Shortcut and raw
--   times reach the same physical state and are centered on their respective
--   mean drifts.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/CriticalEndpointConsequences.lean#L496-L607
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/CriticalEndpointConsequences.lean#L496-L607

import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointNaturalDensity
import Definitions.Def_FirstPassageLinearTransport_PolylogExceptionalCount
import Definitions.Def_FirstPassageLinearTransport_CriticalEndpointConsequences
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.moving_polylogarithmic_common_landing_centered_clocks
    {A : ℕ → ℝ} {Amax c beta N : ℝ}
    (hAmax : 0 < Amax)
    (hc : fixedPolylogClockCritical < c)
    (hbeta : 0 < beta)
    (hN : 0 < N)
    (hbuffer : Tendsto (sharpMovingRankBuffer A) atTop atTop)
    (hUpper : ∀ᶠ M : ℕ in atTop, A M ≤ Amax) :
    ∃ S : Set ℕ, ∃ C : ℝ,
      0 < C ∧ NaturalDensityOne S ∧
      (∀ᶠ M : ℕ in atTop,
        shellExceptionalRatio S M ≤
          C * ((2 : ℝ) ^ (-(sharpMovingRankBuffer A M)) +
            (((M : ℝ) + 2) ^ (-N)))) ∧
      (∀ᶠ n : ℕ in atTop, n ∈ S →
        ∃ k ell : ℕ,
          (k : ℝ) < c * Real.log n ∧
          |driftGap * (k : ℝ) - (Nat.log 2 n : ℝ)| ≤
            C * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
              Real.log ((Nat.log 2 n : ℝ) + 2)) ∧
          |(2 * driftGap / 3) * (ell : ℝ) - (Nat.log 2 n : ℝ)| ≤
            C * Real.sqrt (((Nat.log 2 n : ℝ) + 2) *
              Real.log ((Nat.log 2 n : ℝ) + 2)) ∧
          ell = rawTime n k ∧
          rawOrbit ell n = orbit k n ∧
          (orbit k n : ℝ) <
            C * (Real.log n) ^ (A (Nat.log 2 n)) ∧
          (∀ j : ℕ, j ≤ k →
            (orbit j n : ℝ) ≤
              (n : ℝ) * (((Nat.log 2 n : ℝ) + 2) ^ N)) ∧
          (∀ i : ℕ, i ≤ ell →
            (rawOrbit i n : ℝ) ≤
              (n : ℝ) * (((Nat.log 2 n : ℝ) + 2) ^ N))) := by sorry
