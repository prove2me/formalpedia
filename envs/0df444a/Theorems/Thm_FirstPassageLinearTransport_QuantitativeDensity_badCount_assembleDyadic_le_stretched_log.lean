-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_QuantitativeDensity_badCount_assembleDyadic_le_stretched_log
-- name    : FirstPassageLinearTransport.QuantitativeDensity.badCount_assembleDyadic_le_stretched_log
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:37:35.531551+00:00
-- url     : https://prove2.me/theorems/5bc8faab-8431-4e88-881e-c15c3c4e7fb9
-- title:
--   Quantitative Density: bad Count assemble Dyadic le stretched log
-- statement:
--   Natural-log form of the stretched shell summation.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/StretchedExceptionalCount.lean#L312-L391
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/StretchedExceptionalCount.lean#L312-L391

import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
import Definitions.Def_FirstPassageLinearTransport_StretchedExceptionalCount
set_option autoImplicit true
set_option maxHeartbeats 1000000
open FirstPassageLinearTransport
open FirstPassageLinearTransport.QuantitativeDensity
open scoped Real Topology BigOperators
noncomputable section

theorem FirstPassageLinearTransport.QuantitativeDensity.badCount_assembleDyadic_le_stretched_log
    (S : ℕ → Set ℕ) (M₀ N : ℕ) (A c alpha : ℝ)
    (hA : 0 ≤ A) (hc : 0 < c)
    (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    (hshell :
      ∀ M, M₀ ≤ M →
        shellExceptionalRatio (S M) M ≤
          A * Real.exp
            (-c * (stretchedShellScale M) ^ alpha))
    (hN : 0 < N)
    (hL2 : 2 ≤ Nat.log 2 N)
    (hM₀ : M₀ ≤ (Nat.log 2 N) / 2) :
    (badCount (assembleDyadic S) N : ℝ) ≤
      (1 + 2 * A) * N *
        Real.exp
          (-(stretchedDyadicRate c / 2) *
            (Real.log N) ^ alpha) := by sorry
