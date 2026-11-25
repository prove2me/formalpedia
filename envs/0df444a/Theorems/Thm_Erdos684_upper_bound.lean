-- Prove2me | Theorems.Thm_Erdos684_upper_bound
-- name    : Erdos684.upper_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:48:16.208791+00:00
-- url     : https://prove2.me/theorems/81adf3a6-2780-4a31-bf87-7ba5d1139fdf
-- title:
--   Erdos684: upper bound
-- statement:
--   The known quadratic-logarithmic bound, with the explicit nonoptimal constant `514`.
--
--   Source: https://github.com/AItoBit/erdos-684-elementary-bounds/blob/a59cf65171b19dc7785b767d3b88ad8ef754f3eb/Solution.lean#L25-L54
-- source:
--   https://github.com/AItoBit/erdos-684-elementary-bounds/blob/a59cf65171b19dc7785b767d3b88ad8ef754f3eb/Solution.lean#L25-L54

module
public import Definitions.Def_Erdos684_Lower
public import Definitions.Def_Erdos684_Averaging
public import Definitions.Def_Erdos684_Analytic
public import Definitions.Def_Erdos684ElementaryBounds_Solution
set_option autoImplicit false
@[expose] public section
public section
open Filter Real Finset
open scoped Topology
open Erdos684

theorem Erdos684.upper_bound :
    ∀ᶠ n : ℕ in atTop, ∃ k ≤ n,
      (k : ℝ) ≤ 514 * (log (n : ℝ)) ^ 2 ∧ n ^ 2 < smallPrimePart n k := by sorry
