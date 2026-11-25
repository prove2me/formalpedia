-- Prove2me | Theorems.Thm_Erdos684_eventually_averaging_gap
-- name    : Erdos684.eventually_averaging_gap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:39:55.638243+00:00
-- url     : https://prove2.me/theorems/e9d740dc-aad2-4b17-9fa8-e3f71ddb8a71
-- title:
--   Erdos684: eventually averaging gap
-- statement:
--   The explicit constants leave a positive margin in the finite averaging inequality.
--
--   Source: https://github.com/AItoBit/erdos-684-elementary-bounds/blob/a59cf65171b19dc7785b767d3b88ad8ef754f3eb/Erdos684/Analytic.lean#L160-L178
-- source:
--   https://github.com/AItoBit/erdos-684-elementary-bounds/blob/a59cf65171b19dc7785b767d3b88ad8ef754f3eb/Erdos684/Analytic.lean#L160-L178

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

theorem Erdos684.eventually_averaging_gap :
    ∀ᶠ n : ℕ in atTop,
      4 * (primeCutoff n : ℝ) * log n <
        (windowLength n : ℝ) * (Chebyshev.theta (primeCutoff n) -
          (windowLength n : ℝ) * log ((n + windowLength n : ℕ) : ℝ)) := by sorry
