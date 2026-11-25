-- Prove2me | Theorems.Thm_Erdos679_additive_refutation
-- name    : Erdos679.additive_refutation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:41:21.478844+00:00
-- url     : https://prove2.me/theorems/486c0f86-7ca0-4cc8-b9d1-3b12291dd381
-- title:
--   Erdos679: additive refutation
-- statement:
--   For every additive constant and every lower bound on the shift, all sufficiently
--   large inputs admit a shift violating that additive bound.
--
--   Source: https://github.com/AItoBit/erdos-679-additive-refutation/blob/4a53d358d1b7ade35d6f696f501c99b4d88c9e4c/Solution.lean#L65-L98
-- source:
--   https://github.com/AItoBit/erdos-679-additive-refutation/blob/4a53d358d1b7ade35d6f696f501c99b4d88c9e4c/Solution.lean#L65-L98

module
public import Definitions.Def_Erdos679_Analytic
public import Definitions.Def_Erdos679_Gap
public import Definitions.Def_Erdos679_CRT
public import Definitions.Def_Erdos679AdditiveRefutation_Solution
set_option autoImplicit false
@[expose] public section
public section
open Filter Real
open scoped Topology
open Erdos679

theorem Erdos679.additive_refutation (C : ℝ) (K : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∃ k < n, K < k ∧
      log (k : ℝ) / log (log k) + C ≤
        (ArithmeticFunction.cardDistinctFactors (n - k) : ℝ) := by sorry
