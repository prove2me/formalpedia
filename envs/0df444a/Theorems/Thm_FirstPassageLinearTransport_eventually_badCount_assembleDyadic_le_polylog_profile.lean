-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_eventually_badCount_assembleDyadic_le_polylog_profile
-- name    : FirstPassageLinearTransport.eventually_badCount_assembleDyadic_le_polylog_profile
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:48:11.848026+00:00
-- url     : https://prove2.me/theorems/5f03b968-2bcd-4454-a706-b7ea75854788
-- title:
--   First Passage Linear Transport: eventually bad Count assemble Dyadic le polylog profile
-- statement:
--   Eventual quantitative prefix count with the same half-logarithmic power
--   as the shell profile.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/PolylogExceptionalCount.lean#L270-L302
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/PolylogExceptionalCount.lean#L270-L302

import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
import Definitions.Def_FirstPassageLinearTransport_PolylogExceptionalCount
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology BigOperators
noncomputable section

theorem FirstPassageLinearTransport.eventually_badCount_assembleDyadic_le_polylog_profile
    (S : ℕ → Set ℕ) (M₀ : ℕ) (B kappa : ℝ)
    (hB : 0 ≤ B) (hkappa : 0 ≤ kappa)
    (hshell : ∀ M, M₀ ≤ M →
      shellExceptionalRatio (S M) M ≤
        B * (((M : ℝ) + 2) ^ (-kappa))) :
    ∀ᶠ N : ℕ in atTop,
      (badCount (assembleDyadic S) N : ℝ) ≤
        (1 + 2 * B) * N *
          ((((Nat.log 2 N) / 2 : ℕ) : ℝ) + 2) ^ (-kappa) := by sorry
