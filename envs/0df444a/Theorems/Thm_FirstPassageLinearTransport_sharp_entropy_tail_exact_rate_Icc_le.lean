-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_sharp_entropy_tail_exact_rate_Icc_le
-- name    : FirstPassageLinearTransport.sharp_entropy_tail_exact_rate_Icc_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:21:13.628444+00:00
-- url     : https://prove2.me/theorems/05efbd3c-a075-42ef-89fe-e70c504e085a
-- title:
--   First Passage Linear Transport: sharp entropy tail exact rate Icc le
-- statement:
--   Exact-rate entropy tail.  The terminal factor retains the actual rate
--   `b`; the lower rate `b₀` is used only in the translated geometric series.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/MovingSharpTail.lean#L245-L309
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/MovingSharpTail.lean#L245-L309

import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Order.Interval.Finset.SuccPred
import Definitions.Def_FirstPassageLinearTransport_TerminalTail
import Definitions.Def_FirstPassageLinearTransport_MovingSharpTail
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped BigOperators Real Topology
noncomputable section

theorem FirstPassageLinearTransport.sharp_entropy_tail_exact_rate_Icc_le
    {b₀ b : ℝ} (hb₀ : 0 < b₀) (hb₀b : b₀ ≤ b)
    {L U : ℕ} (hL : 2 ≤ L) (hLU : L ≤ U) :
    ∑ q ∈ Finset.Icc L U,
        ((q + 1 : ℕ) : ℝ) / Real.sqrt ((q - 1 : ℕ) : ℝ) *
          Real.exp (-(b * ((q - 1 : ℕ) : ℝ))) ≤
      3 * Real.sqrt L * Real.exp (-(b * ((L - 1 : ℕ) : ℝ))) *
        weightedTailConstant b₀ (b₀ / 2) := by sorry
