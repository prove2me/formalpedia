-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_badCount_assembleDyadic_le_polylog_profile
-- name    : FirstPassageLinearTransport.badCount_assembleDyadic_le_polylog_profile
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:19:45.239858+00:00
-- url     : https://prove2.me/theorems/e0c5a020-f687-4849-b957-0eb133047105
-- title:
--   First Passage Linear Transport: bad Count assemble Dyadic le polylog profile
-- statement:
--   Exact early/late dyadic decomposition for a polynomial shell profile.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/PolylogExceptionalCount.lean#L24-L147
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/PolylogExceptionalCount.lean#L24-L147

import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
import Definitions.Def_FirstPassageLinearTransport_PolylogExceptionalCount
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology BigOperators
noncomputable section

theorem FirstPassageLinearTransport.badCount_assembleDyadic_le_polylog_profile
    (S : ℕ → Set ℕ) (M₀ N : ℕ) (B kappa : ℝ)
    (hB : 0 ≤ B) (hkappa : 0 ≤ kappa)
    (hshell : ∀ M, M₀ ≤ M →
      shellExceptionalRatio (S M) M ≤
        B * (((M : ℝ) + 2) ^ (-kappa)))
    (hN : 0 < N) (hM₀ : M₀ ≤ (Nat.log 2 N) / 2) :
    (badCount (assembleDyadic S) N : ℝ) ≤
      (2 : ℝ) ^ ((Nat.log 2 N) / 2) +
        2 * B * N *
          ((((Nat.log 2 N) / 2 : ℕ) : ℝ) + 2) ^ (-kappa) := by sorry
