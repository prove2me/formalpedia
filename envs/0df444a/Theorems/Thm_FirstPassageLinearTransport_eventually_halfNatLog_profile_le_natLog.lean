-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_eventually_halfNatLog_profile_le_natLog
-- name    : FirstPassageLinearTransport.eventually_halfNatLog_profile_le_natLog
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:48:21.140156+00:00
-- url     : https://prove2.me/theorems/e9fe013c-8cc8-5394-af0a-d760f038b75c
-- title:
--   First Passage Linear Transport: eventually half Nat Log profile le nat Log
-- statement:
--   The explicit half-base-two-logarithmic scale is eventually bounded by
--   the corresponding negative power of the natural logarithm.  The constant
--   `(2 * log 2)^kappa` records the entire change of logarithm and the half-shell
--   split.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/PolylogExceptionalCount.lean#L308-L360
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/PolylogExceptionalCount.lean#L308-L360

import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
import Definitions.Def_FirstPassageLinearTransport_PolylogExceptionalCount
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology BigOperators
noncomputable section

theorem FirstPassageLinearTransport.eventually_halfNatLog_profile_le_natLog
    {kappa : ℝ} (hkappa : 0 ≤ kappa) :
    ∀ᶠ N : ℕ in atTop,
      ((((Nat.log 2 N) / 2 : ℕ) : ℝ) + 2) ^ (-kappa) ≤
        (2 * Real.log 2) ^ kappa * (Real.log N) ^ (-kappa) := by sorry
