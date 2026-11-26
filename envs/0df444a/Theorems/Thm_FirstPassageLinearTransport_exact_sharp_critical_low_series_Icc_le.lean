-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_exact_sharp_critical_low_series_Icc_le
-- name    : FirstPassageLinearTransport.exact_sharp_critical_low_series_Icc_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:21:14.511546+00:00
-- url     : https://prove2.me/theorems/ec267108-d4e8-5491-96e8-f4c6a4b56e81
-- title:
--   First Passage Linear Transport: exact sharp critical low series Icc le
-- statement:
--   Combined dyadic and entropy tails at their exact leading rates.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/MovingSharpTail.lean#L312-L360
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/MovingSharpTail.lean#L312-L360

import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Order.Interval.Finset.SuccPred
import Definitions.Def_FirstPassageLinearTransport_TerminalTail
import Definitions.Def_FirstPassageLinearTransport_MovingSharpTail
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped BigOperators Real Topology
noncomputable section

theorem FirstPassageLinearTransport.exact_sharp_critical_low_series_Icc_le
    {b₀ b Cpref : ℝ} (hb₀ : 0 < b₀) (hb₀b : b₀ ≤ b)
    (hCpref : 0 ≤ Cpref) {L U : ℕ} (hL : 2 ≤ L) (hLU : L ≤ U) :
    ∑ q ∈ Finset.Icc L U,
        ((q + 1 : ℕ) : ℝ) *
          (Real.exp (-(Real.log 2 * (q : ℝ))) +
            Cpref / Real.sqrt ((q - 1 : ℕ) : ℝ) *
              Real.exp (-(b * ((q - 1 : ℕ) : ℝ)))) ≤
      weightedTailConstant (Real.log 2) (Real.log 2 / 2) *
          ((L + 1 : ℕ) : ℝ) * Real.exp (-(Real.log 2 * (L : ℝ))) +
        3 * Cpref * weightedTailConstant b₀ (b₀ / 2) *
          Real.sqrt L * Real.exp (-(b * ((L - 1 : ℕ) : ℝ))) := by sorry
