-- Prove2me | Theorems.Thm_AvramDividend_Classical_deriv_deriv_eq_zero_of_mem_cstarSet
-- name    : AvramDividend.Classical.deriv_deriv_eq_zero_of_mem_cstarSet
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T07:08:41.908161+00:00
-- url     : https://prove2.me/theorems/4f242690-ba0b-4ca8-8311-527b00397395
-- title:
--   A positive optimal-barrier minimiser has vanishing second scale derivative
-- statement:
--   If a is a member of the exact formal cstarSet W, so a>0 and the ordinary derivative W'(a) is globally minimal amongst all positive arguments, then the ordinary derivative of W' vanishes at a. This is Fermat's local-minimum theorem with Lean's totalised deriv and does not itself establish that (cstar W).toReal belongs to cstarSet. It is a precise, small second-order matching input for Gaussian barrier smooth fit.

import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Order.LocalExtr
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.deriv_deriv_eq_zero_of_mem_cstarSet (W : ℝ → ℝ) (a : ℝ)
    (ha : a ∈ cstarSet W) : deriv (deriv W) a = 0 := by sorry
