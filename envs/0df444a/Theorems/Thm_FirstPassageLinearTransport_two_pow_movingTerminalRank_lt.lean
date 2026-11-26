-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_two_pow_movingTerminalRank_lt
-- name    : FirstPassageLinearTransport.two_pow_movingTerminalRank_lt
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:24:10.836384+00:00
-- url     : https://prove2.me/theorems/d6984577-1dab-575a-96ce-95d9ca177afa
-- title:
--   First Passage Linear Transport: two pow moving Terminal Rank lt
-- statement:
--   The terminal-rank ceiling costs only a factor two, pointwise in the
--   moving exponent.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/MovingEndpointScalars.lean#L71-L88
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/MovingEndpointScalars.lean#L71-L88

import Definitions.Def_FirstPassageLinearTransport_ShrinkingParameters
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
import Definitions.Def_FirstPassageLinearTransport_MovingEndpointScalars
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.two_pow_movingTerminalRank_lt
    {A : ℕ → ℝ} {M : ℕ} (hA : 0 ≤ A M) :
    ((2 ^ movingTerminalRank A M : ℕ) : ℝ) <
      2 * (((M : ℝ) + 2) ^ (A M)) := by sorry
