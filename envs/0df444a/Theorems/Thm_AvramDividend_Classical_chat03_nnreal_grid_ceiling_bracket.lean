-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_nnreal_grid_ceiling_bracket
-- name    : AvramDividend.Classical.chat03_nnreal_grid_ceiling_bracket
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T19:55:51.209973+00:00
-- url     : https://prove2.me/theorems/15e09c24-2f6f-4b3e-8446-49353fbbb197
-- title:
--   First ceiling mesh sample after a nonnegative real time has strictly less than one mesh-step delay
-- statement:
--   For a nonnegative real time t and positive grid spacing h, k=Nat.ceil(t/h) gives t≤k*h<t+h directly in nonnegative real time ℝ≥0. This is the clock-space version of the independently Proved real ceiling mesh estimate and can be combined without coercion assumptions with the accepted right interval of a strict Lévy exit, giving detection by a sufficiently small mesh. There are no stochastic, scale-function or filtration assumptions.
-- source:
--   Pinned Mathlib Basic.NNReal.Basic FloorSemiring instance, Nat.le_ceil and Nat.ceil_lt_add_one; Chat 03 direct finite dyadic exit proof, revision 0df444a360eaa60ab8c11dca51a86af692955474.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.FieldSimp

open MeasureTheory Filter Set Topology
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_nnreal_grid_ceiling_bracket
    (t h : ℝ≥0) (hh : 0 < h) :
    t ≤ (Nat.ceil (t / h) : ℝ≥0) * h ∧
      (Nat.ceil (t / h) : ℝ≥0) * h < t + h := by sorry
