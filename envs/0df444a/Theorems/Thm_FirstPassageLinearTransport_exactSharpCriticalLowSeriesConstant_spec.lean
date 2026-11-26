-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_exactSharpCriticalLowSeriesConstant_spec
-- name    : FirstPassageLinearTransport.exactSharpCriticalLowSeriesConstant_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:21:47.281089+00:00
-- url     : https://prove2.me/theorems/df0c5292-e529-4d56-bc85-b2069a8fcd8f
-- title:
--   First Passage Linear Transport: exact Sharp Critical Low Series Constant spec
-- statement:
--   Uniform exact-rate critical-tail estimate for the canonical constant.
--   The terminal exponential retains every actual `b ≥ b₀`.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/MovingSharpTail.lean#L370-L441
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/MovingSharpTail.lean#L370-L441

import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Order.Interval.Finset.SuccPred
import Definitions.Def_FirstPassageLinearTransport_TerminalTail
import Definitions.Def_FirstPassageLinearTransport_MovingSharpTail
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped BigOperators Real Topology
noncomputable section

theorem FirstPassageLinearTransport.exactSharpCriticalLowSeriesConstant_spec
    {b₀ Cpref : ℝ} (hb₀ : 0 < b₀) (hCpref : 0 ≤ Cpref) :
    0 < exactSharpCriticalLowSeriesConstant b₀ Cpref ∧
      ∀ {b : ℝ}, b₀ ≤ b → ∀ {L U : ℕ},
      2 ≤ L → L ≤ U →
      ∑ q ∈ Finset.Icc L U,
          ((q + 1 : ℕ) : ℝ) *
            (Real.exp (-(Real.log 2 * (q : ℝ))) +
              Cpref / Real.sqrt ((q - 1 : ℕ) : ℝ) *
                Real.exp (-(b * ((q - 1 : ℕ) : ℝ)))) ≤
        exactSharpCriticalLowSeriesConstant b₀ Cpref *
          (((L + 1 : ℕ) : ℝ) * Real.exp (-(Real.log 2 * (L : ℝ))) +
          Real.sqrt L * Real.exp (-(b * ((L - 1 : ℕ) : ℝ)))) := by sorry
