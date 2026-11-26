-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_oddCount_upper_of_initialWindowGood
-- name    : FirstPassageLinearTransport.oddCount_upper_of_initialWindowGood
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:56:17.423048+00:00
-- url     : https://prove2.me/theorems/b5babfad-2cd4-5c5b-8152-58b10d867a1b
-- title:
--   First Passage Linear Transport: odd Count upper of initial Window Good
-- statement:
--   The upper orbit envelope bounds the odd-count excess of every retained
--   shortcut prefix.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/RawClockBudget.lean#L26-L67
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/RawClockBudget.lean#L26-L67

import Definitions.Def_FirstPassageLinearTransport_RawDynamics
import Definitions.Def_FirstPassageLinearTransport_ClockBudget
import Definitions.Def_FirstPassageLinearTransport_RawClockBudget
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.oddCount_upper_of_initialWindowGood
    {eta : ℝ} {n k : ℕ}
    (hn : 0 < n) (hnGood : n ∈ initialWindowGood eta)
    (hk : k ≤ Nat.log 2 n) :
    (oddCount n k : ℝ) ≤
      (k : ℝ) / 2 + eta * Real.log n / Real.log 3 := by sorry
