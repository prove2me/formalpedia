-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_orbit_scaled_lt_two_mul_parity
-- name    : FirstPassageLinearTransport.orbit_scaled_lt_two_mul_parity
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:25:39.815641+00:00
-- url     : https://prove2.me/theorems/f4b3fd22-13d1-4958-8bb5-02c8c682f5e5
-- title:
--   First Passage Linear Transport: orbit scaled lt two mul parity
-- statement:
--   Up to its shell-rank horizon, the exact affine iterate is bounded by
--   twice its pure multiplicative parity term.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutDensity.lean#L46-L61
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutDensity.lean#L46-L61

import Definitions.Def_FirstPassageLinearTransport_TimeoutCore
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section

theorem FirstPassageLinearTransport.orbit_scaled_lt_two_mul_parity
    {m x j : ℕ} (hx : x ∈ dyadicShell m) (hj : j ≤ m) :
    2 ^ j * orbit j x < 2 * 3 ^ oddCount x j * x := by sorry
