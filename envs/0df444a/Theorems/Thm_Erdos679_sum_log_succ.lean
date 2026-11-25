-- Prove2me | Theorems.Thm_Erdos679_sum_log_succ
-- name    : Erdos679.sum_log_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:11:02.62621+00:00
-- url     : https://prove2.me/theorems/3ba24b55-d679-4680-ae17-92f75dfb5640
-- title:
--   Erdos679: sum log succ
-- statement:
--   The Erdos679 construction uses the sum log succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/AItoBit/erdos-679-additive-refutation/blob/4a53d358d1b7ade35d6f696f501c99b4d88c9e4c/Erdos679/Analytic.lean#L154-L161
-- source:
--   https://github.com/AItoBit/erdos-679-additive-refutation/blob/4a53d358d1b7ade35d6f696f501c99b4d88c9e4c/Erdos679/Analytic.lean#L154-L161

module
public import Definitions.Def_Erdos679_StirlingBound
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Lean.Elab.Tactic.Omega
public import Definitions.Def_Erdos679_Analytic
set_option autoImplicit false
@[expose] public section
public section
open Filter Real
open scoped Topology
open Erdos679

theorem Erdos679.sum_log_succ (m : ℕ) :
    ∑ i ∈ Finset.range m, log ((i + 1 : ℕ) : ℝ) = log (m.factorial : ℝ) := by sorry
