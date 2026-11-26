-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_shifted_linear_exp_Icc_le
-- name    : FirstPassageLinearTransport.shifted_linear_exp_Icc_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:18:55.171903+00:00
-- url     : https://prove2.me/theorems/08afa1a9-a9ef-4e3f-9962-b8a2926f196f
-- title:
--   First Passage Linear Transport: shifted linear exp Icc le
-- statement:
--   Shifted linear exponential tails retain the original rate.  The rate
--   `c₀` is used only to control the translated geometric series; the leading
--   factor keeps the actual rate `c`.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/MovingSharpTail.lean#L50-L148
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/MovingSharpTail.lean#L50-L148

import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Order.Interval.Finset.SuccPred
import Definitions.Def_FirstPassageLinearTransport_TerminalTail
import Definitions.Def_FirstPassageLinearTransport_MovingSharpTail
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped BigOperators Real Topology
noncomputable section

theorem FirstPassageLinearTransport.shifted_linear_exp_Icc_le
    {c₀ c : ℝ} (hc₀ : 0 < c₀) (hc₀c : c₀ ≤ c)
    {L U : ℕ} (hLU : L ≤ U) :
    ∑ q ∈ Finset.Icc L U,
        ((q + 1 : ℕ) : ℝ) * Real.exp (-(c * (q : ℝ))) ≤
      ((L + 1 : ℕ) : ℝ) * Real.exp (-(c * (L : ℝ))) *
        weightedTailConstant c₀ (c₀ / 2) := by sorry
