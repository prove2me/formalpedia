-- Prove2me | Theorems.Thm_Erdos679_finite_window_lifting
-- name    : Erdos679.finite_window_lifting
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T15:01:20.79575+00:00
-- url     : https://prove2.me/theorems/75b1a8d4-7a85-4337-ac83-e9392e1ac73f
-- title:
--   Erdos679: finite window lifting
-- statement:
--   A complete residue window gives a suitable shift for each input beyond that window.
--
--   Source: https://github.com/AItoBit/erdos-679-additive-refutation/blob/4a53d358d1b7ade35d6f696f501c99b4d88c9e4c/Erdos679/CRT.lean#L39-L54
-- source:
--   https://github.com/AItoBit/erdos-679-additive-refutation/blob/4a53d358d1b7ade35d6f696f501c99b4d88c9e4c/Erdos679/CRT.lean#L39-L54

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

theorem Erdos679.finite_window_lifting (M K : ℕ) (hM : 0 < M) (F : ℕ → ℝ) (C : ℝ)
    (hwindow : ∀ k, K < k → k ≤ K + M →
      F k + C ≤ (ArithmeticFunction.cardDistinctFactors M : ℝ))
    {n : ℕ} (hn : K + M < n) :
    ∃ k < n, K < k ∧ F k + C ≤ (ArithmeticFunction.cardDistinctFactors (n - k) : ℝ) := by sorry
