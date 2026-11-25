-- Prove2me | Theorems.Thm_Erdos679_log_primeProduct_le_sum
-- name    : Erdos679.log_primeProduct_le_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:20:04.721063+00:00
-- url     : https://prove2.me/theorems/26d4620a-583b-5702-a82a-4bb915a4caea
-- title:
--   Erdos679: log prime Product le sum
-- statement:
--   A finite initial segment contributes a constant to the prime-log sum.
--
--   Source: https://github.com/AItoBit/erdos-679-additive-refutation/blob/4a53d358d1b7ade35d6f696f501c99b4d88c9e4c/Erdos679/Analytic.lean#L164-L209
-- source:
--   https://github.com/AItoBit/erdos-679-additive-refutation/blob/4a53d358d1b7ade35d6f696f501c99b4d88c9e4c/Erdos679/Analytic.lean#L164-L209

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

theorem Erdos679.log_primeProduct_le_sum (N : ℕ) (hN : 2 ≤ N)
    (hp : ∀ i ≥ N, (Nat.nth Nat.Prime i : ℝ) ≤ (3 / 2 : ℝ) * i * log i)
    {m : ℕ} (hm : N ≤ m) (hlog : 1 ≤ log m) :
    log (primeProduct m : ℝ) ≤ log (primeProduct N : ℝ) + log (m.factorial : ℝ) +
      m * (log (3 / 2 : ℝ) + log (log m)) := by sorry
