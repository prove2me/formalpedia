-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_collatzBallot_denominator_lower
-- name    : FirstPassageLinearTransport.collatzBallot_denominator_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:36:24.243863+00:00
-- url     : https://prove2.me/theorems/4e7205d2-d07f-4730-9571-2e8b1dd7b0e6
-- title:
--   First Passage Linear Transport: collatz Ballot denominator lower
-- statement:
--   The exact square-root denominator supplied by the quarter-scale split is
--   bounded below by `m^(3/2)/16`.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L2415-L2442
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L2415-L2442

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.collatzBallot_denominator_lower {m : ℕ} (hm : 8 ≤ m) :
    (m : ℝ) * Real.sqrt m / 16 ≤
      Real.sqrt (collatzBallotOuterLength m) *
        Real.sqrt (collatzBallotOuterLength m) *
          Real.sqrt (collatzBallotMiddleLength m) := by sorry
