-- Prove2me | Theorems.Thm_Erdos679_eventually_finite_window_lifting
-- name    : Erdos679.eventually_finite_window_lifting
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:01:21.598702+00:00
-- url     : https://prove2.me/theorems/b78340b2-4ddc-5353-b8ef-1d54401433c4
-- title:
--   Erdos679: eventually finite window lifting
-- statement:
--   The finite-window hypothesis is sufficient for an eventual lower bound.
--
--   Source: https://github.com/AItoBit/erdos-679-additive-refutation/blob/4a53d358d1b7ade35d6f696f501c99b4d88c9e4c/Erdos679/CRT.lean#L57-L65
-- source:
--   https://github.com/AItoBit/erdos-679-additive-refutation/blob/4a53d358d1b7ade35d6f696f501c99b4d88c9e4c/Erdos679/CRT.lean#L57-L65

module
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Lean.Elab.Tactic.Omega
public import Definitions.Def_Erdos679_CRT
set_option autoImplicit false
@[expose] public section
public section
open Erdos679

theorem Erdos679.eventually_finite_window_lifting (M K : ℕ) (hM : 0 < M) (F : ℕ → ℝ) (C : ℝ)
    (hwindow : ∀ k, K < k → k ≤ K + M →
      F k + C ≤ (ArithmeticFunction.cardDistinctFactors M : ℝ)) :
    ∀ᶠ n in Filter.atTop,
      ∃ k < n, K < k ∧ F k + C ≤ (ArithmeticFunction.cardDistinctFactors (n - k) : ℝ) := by sorry
