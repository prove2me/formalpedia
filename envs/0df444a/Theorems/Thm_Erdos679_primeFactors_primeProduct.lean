-- Prove2me | Theorems.Thm_Erdos679_primeFactors_primeProduct
-- name    : Erdos679.primeFactors_primeProduct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:20:06.242617+00:00
-- url     : https://prove2.me/theorems/e2d2a9bd-9615-53a9-8d98-7c91d0bc09be
-- title:
--   Erdos679: prime Factors prime Product
-- statement:
--   The Erdos679 construction uses the prime Factors prime Product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/AItoBit/erdos-679-additive-refutation/blob/4a53d358d1b7ade35d6f696f501c99b4d88c9e4c/Erdos679/Analytic.lean#L247-L255
-- source:
--   https://github.com/AItoBit/erdos-679-additive-refutation/blob/4a53d358d1b7ade35d6f696f501c99b4d88c9e4c/Erdos679/Analytic.lean#L247-L255

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

theorem Erdos679.primeFactors_primeProduct (m : ℕ) :
    (primeProduct m).primeFactors =
      (Finset.range m).image (fun i => Nat.nth Nat.Prime i) := by sorry
