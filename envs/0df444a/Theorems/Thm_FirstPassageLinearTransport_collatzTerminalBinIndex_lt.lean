-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_collatzTerminalBinIndex_lt
-- name    : FirstPassageLinearTransport.collatzTerminalBinIndex_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:39:47.589116+00:00
-- url     : https://prove2.me/theorems/fb93d2e6-290d-51eb-b0dd-29264d573c6d
-- title:
--   First Passage Linear Transport: collatz Terminal Bin Index lt
-- statement:
--   The canonical terminal bin lies in a finite range depending only on the
--   word length and the barrier.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutDensity.lean#L271-L280
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutDensity.lean#L271-L280

import Definitions.Def_FirstPassageLinearTransport_TimeoutCore
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section

theorem FirstPassageLinearTransport.collatzTerminalBinIndex_lt
    {m : ℕ} {B : ℝ} {v : Fin m → Bool}
    (hnonneg : 0 ≤ B + wordIncrementSum collatzLogIncrement v) :
    collatzTerminalBinIndex B v < m + ⌈B⌉₊ + 2 := by sorry
