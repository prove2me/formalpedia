-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_rawTime_add_exact_halving
-- name    : FirstPassageLinearTransport.rawTime_add_exact_halving
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:47:41.82286+00:00
-- url     : https://prove2.me/theorems/c7b1b349-cc38-5300-a1de-3ecdbfff8708
-- title:
--   First Passage Linear Transport: raw Time add exact halving
-- statement:
--   Exact halving after a shortcut prefix adds one raw step per halving and
--   no extra odd raw step.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutRawClock.lean#L199-L204
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutRawClock.lean#L199-L204

import Definitions.Def_FirstPassageLinearTransport_TimeoutOrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.rawTime_add_exact_halving
    {n elapsed q v : ℕ} (heq : orbit elapsed n = 2 ^ q) (hv : v ≤ q) :
    rawTime n (elapsed + v) = rawTime n elapsed + v := by sorry
