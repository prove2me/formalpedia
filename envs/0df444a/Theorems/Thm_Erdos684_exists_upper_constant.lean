-- Prove2me | Theorems.Thm_Erdos684_exists_upper_constant
-- name    : Erdos684.exists_upper_constant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T16:03:26.43235+00:00
-- url     : https://prove2.me/theorems/8b8248c5-dec3-5a4f-a787-e5b02abd744a
-- title:
--   Erdos684: exists upper constant
-- statement:
--   There is an absolute quadratic-logarithmic bound on an index with large small-prime part.
--
--   Source: https://github.com/AItoBit/erdos-684-elementary-bounds/blob/a59cf65171b19dc7785b767d3b88ad8ef754f3eb/Solution.lean#L57-L60
-- source:
--   https://github.com/AItoBit/erdos-684-elementary-bounds/blob/a59cf65171b19dc7785b767d3b88ad8ef754f3eb/Solution.lean#L57-L60

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

theorem Erdos684.exists_upper_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∃ k ≤ n,
      (k : ℝ) ≤ C * (log (n : ℝ)) ^ 2 ∧ n ^ 2 < smallPrimePart n k := by sorry
