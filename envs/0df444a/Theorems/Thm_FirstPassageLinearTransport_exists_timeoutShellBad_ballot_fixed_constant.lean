-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_exists_timeoutShellBad_ballot_fixed_constant
-- name    : FirstPassageLinearTransport.exists_timeoutShellBad_ballot_fixed_constant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:25:28.52028+00:00
-- url     : https://prove2.me/theorems/58114180-8d02-5938-8763-b2d3a4bef46b
-- title:
--   First Passage Linear Transport: exists timeout Shell Bad ballot fixed constant
-- statement:
--   Fixed-parameter form of the ballot timeout estimate.  The barrier and
--   terminal-bin constants are absorbed once `K₀` and the low-window multiplier
--   `C` are fixed.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutDensity.lean#L848-L883
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutDensity.lean#L848-L883

import Definitions.Def_FirstPassageLinearTransport_TimeoutCore
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section

theorem FirstPassageLinearTransport.exists_timeoutShellBad_ballot_fixed_constant
    (K₀ C : ℝ) (hK₀ : 0 ≤ K₀) (hC : 0 ≤ C) :
    ∃ D : ℝ, 0 < D ∧
      ∀ L m : ℕ,
        0 < L → L ≤ m → (m : ℝ) ≤ C * (L : ℝ) →
        timeoutTargetRank K₀ L m ≤ m → 8 ≤ m →
        ((timeoutShellBad K₀ L m).card : ℝ) / (2 : ℝ) ^ m ≤
          D / ((m : ℝ) * Real.sqrt m) *
            Real.exp (-(firstPassageEndpointRate * (m : ℝ))) := by sorry
