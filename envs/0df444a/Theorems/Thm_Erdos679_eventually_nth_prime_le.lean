-- Prove2me | Theorems.Thm_Erdos679_eventually_nth_prime_le
-- name    : Erdos679.eventually_nth_prime_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:10:59.810291+00:00
-- url     : https://prove2.me/theorems/128e8c57-4a54-4b55-b26f-4bf14ac1488a
-- title:
--   Erdos679: eventually nth prime le
-- statement:
--   Chebyshev's elementary bound gives a constant strictly below $e$ in the
--   upper bound for the $n$th prime.
--
--   Source: https://github.com/AItoBit/erdos-679-additive-refutation/blob/4a53d358d1b7ade35d6f696f501c99b4d88c9e4c/Erdos679/Analytic.lean#L99-L127
-- source:
--   https://github.com/AItoBit/erdos-679-additive-refutation/blob/4a53d358d1b7ade35d6f696f501c99b4d88c9e4c/Erdos679/Analytic.lean#L99-L127

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

theorem Erdos679.eventually_nth_prime_le :
    ∀ᶠ n : ℕ in atTop, (Nat.nth Nat.Prime n : ℝ) ≤
      (3 / 2 : ℝ) * n * log n := by sorry
