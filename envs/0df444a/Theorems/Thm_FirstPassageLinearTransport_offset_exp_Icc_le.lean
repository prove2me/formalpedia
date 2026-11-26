-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_offset_exp_Icc_le
-- name    : FirstPassageLinearTransport.offset_exp_Icc_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:21:26.675841+00:00
-- url     : https://prove2.me/theorems/3f6b9775-2198-4d3f-8a43-56e93717c58d
-- title:
--   First Passage Linear Transport: offset exp Icc le
-- statement:
--   After the translation `q = L + j`, the offset-weighted exponential tail
--   is uniformly bounded.  As in `shifted_linear_exp_Icc_le`, `c₀` controls
--   only the translated tail; no loss is made in the actual rate `c`.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/MovingSharpTail.lean#L153-L179
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/MovingSharpTail.lean#L153-L179

import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Order.Interval.Finset.SuccPred
import Definitions.Def_FirstPassageLinearTransport_TerminalTail
import Definitions.Def_FirstPassageLinearTransport_MovingSharpTail
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped BigOperators Real Topology
noncomputable section

theorem FirstPassageLinearTransport.offset_exp_Icc_le
    {c₀ c : ℝ} (hc₀ : 0 < c₀) (hc₀c : c₀ ≤ c)
    {L U : ℕ} (hLU : L ≤ U) :
    ∑ q ∈ Finset.Icc L U,
        ((q - L + 1 : ℕ) : ℝ) *
          Real.exp (-(c * ((q - L : ℕ) : ℝ))) ≤
      weightedTailConstant c₀ (c₀ / 2) := by sorry
