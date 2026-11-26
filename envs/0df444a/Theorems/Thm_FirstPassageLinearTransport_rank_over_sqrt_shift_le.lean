-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_rank_over_sqrt_shift_le
-- name    : FirstPassageLinearTransport.rank_over_sqrt_shift_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:21:11.510295+00:00
-- url     : https://prove2.me/theorems/64c41051-61ba-4a23-b20b-f7b792ad912c
-- title:
--   First Passage Linear Transport: rank over sqrt shift le
-- statement:
--   The rank factor produced by reverse loss retains only a square-root
--   terminal prefactor after translation to `j = q-L`.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/MovingSharpTail.lean#L183-L241
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/MovingSharpTail.lean#L183-L241

import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Order.Interval.Finset.SuccPred
import Definitions.Def_FirstPassageLinearTransport_TerminalTail
import Definitions.Def_FirstPassageLinearTransport_MovingSharpTail
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped BigOperators Real Topology
noncomputable section

theorem FirstPassageLinearTransport.rank_over_sqrt_shift_le
    {L q : ℕ} (hL : 2 ≤ L) (hLq : L ≤ q) :
    ((q + 1 : ℕ) : ℝ) / Real.sqrt ((q - 1 : ℕ) : ℝ) ≤
      3 * Real.sqrt L * ((q - L + 1 : ℕ) : ℝ) := by sorry
