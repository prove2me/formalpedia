-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_eventually_two_pow_halfNatLog_le_polylog
-- name    : FirstPassageLinearTransport.eventually_two_pow_halfNatLog_le_polylog
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:19:54.692902+00:00
-- url     : https://prove2.me/theorems/351de685-a9b2-5af4-aa76-a505794eb6bd
-- title:
--   First Passage Linear Transport: eventually two pow half Nat Log le polylog
-- statement:
--   The early half of a dyadic prefix is eventually absorbed by every fixed
--   negative power of the half-shell rank.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/PolylogExceptionalCount.lean#L166-L266
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/PolylogExceptionalCount.lean#L166-L266

import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
import Definitions.Def_FirstPassageLinearTransport_PolylogExceptionalCount
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology BigOperators
noncomputable section

theorem FirstPassageLinearTransport.eventually_two_pow_halfNatLog_le_polylog
    {kappa : ℝ} (_hkappa : 0 ≤ kappa) :
    ∀ᶠ N : ℕ in atTop,
      (2 : ℝ) ^ ((Nat.log 2 N) / 2) ≤
        (N : ℝ) *
          ((((Nat.log 2 N) / 2 : ℕ) : ℝ) + 2) ^ (-kappa) := by sorry
