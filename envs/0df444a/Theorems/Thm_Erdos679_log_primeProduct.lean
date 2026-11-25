-- Prove2me | Theorems.Thm_Erdos679_log_primeProduct
-- name    : Erdos679.log_primeProduct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:10:59.747661+00:00
-- url     : https://prove2.me/theorems/29250ae2-195c-47f3-8d51-b2bd50ae2e83
-- title:
--   Erdos679: log prime Product
-- statement:
--   The Erdos679 construction uses the log prime Product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/AItoBit/erdos-679-additive-refutation/blob/4a53d358d1b7ade35d6f696f501c99b4d88c9e4c/Erdos679/Analytic.lean#L148-L152
-- source:
--   https://github.com/AItoBit/erdos-679-additive-refutation/blob/4a53d358d1b7ade35d6f696f501c99b4d88c9e4c/Erdos679/Analytic.lean#L148-L152

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

theorem Erdos679.log_primeProduct (m : ℕ) :
    log (primeProduct m : ℝ) = ∑ i ∈ Finset.range m, log (Nat.nth Nat.Prime i) := by sorry
