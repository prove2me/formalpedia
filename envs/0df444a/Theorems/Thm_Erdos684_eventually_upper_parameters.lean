-- Prove2me | Theorems.Thm_Erdos684_eventually_upper_parameters
-- name    : Erdos684.eventually_upper_parameters
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:19:57.943839+00:00
-- url     : https://prove2.me/theorems/6bde4448-bcbe-4350-911e-95df0a786e68
-- title:
--   Erdos684: eventually upper parameters
-- statement:
--   Bounds for the two rounded parameters used by the finite averaging argument.
--
--   Source: https://github.com/AItoBit/erdos-684-elementary-bounds/blob/a59cf65171b19dc7785b767d3b88ad8ef754f3eb/Erdos684/Analytic.lean#L98-L157
-- source:
--   https://github.com/AItoBit/erdos-684-elementary-bounds/blob/a59cf65171b19dc7785b767d3b88ad8ef754f3eb/Erdos684/Analytic.lean#L98-L157

module
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Lean.Elab.Tactic.Omega
public import Definitions.Def_Erdos684_Analytic
set_option autoImplicit false
@[expose] public section
open Filter Real
open scoped Topology
public section
open Erdos684

theorem Erdos684.eventually_upper_parameters :
    ∀ᶠ n : ℕ in atTop,
      1 ≤ log (n : ℝ) ∧
      0 < n ∧
      2 * primeCutoff n ≤ n ∧
      windowLength n ≤ n ∧
      32 * log (n : ℝ) ≤ (windowLength n : ℝ) ∧
      (windowLength n : ℝ) ≤ 33 * log (n : ℝ) ∧
      256 * (log (n : ℝ)) ^ 2 ≤ (primeCutoff n : ℝ) ∧
      (primeCutoff n : ℝ) ≤ 257 * (log (n : ℝ)) ^ 2 ∧
      log ((n + windowLength n : ℕ) : ℝ) ≤ 2 * log (n : ℝ) ∧
      (primeCutoff n : ℝ) / 2 ≤ Chebyshev.theta (primeCutoff n) ∧
      (2 * primeCutoff n : ℝ) ≤ 514 * (log (n : ℝ)) ^ 2 := by sorry
