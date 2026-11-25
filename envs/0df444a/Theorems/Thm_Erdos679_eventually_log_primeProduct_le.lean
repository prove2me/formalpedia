-- Prove2me | Theorems.Thm_Erdos679_eventually_log_primeProduct_le
-- name    : Erdos679.eventually_log_primeProduct_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:20:22.818552+00:00
-- url     : https://prove2.me/theorems/978491fb-cbc7-4039-ad39-3d48b15d0da1
-- title:
--   Erdos679: eventually log prime Product le
-- statement:
--   The prime product has a fixed linear saving beyond its leading two terms.
--
--   Source: https://github.com/AItoBit/erdos-679-additive-refutation/blob/4a53d358d1b7ade35d6f696f501c99b4d88c9e4c/Erdos679/Analytic.lean#L212-L232
-- source:
--   https://github.com/AItoBit/erdos-679-additive-refutation/blob/4a53d358d1b7ade35d6f696f501c99b4d88c9e4c/Erdos679/Analytic.lean#L212-L232

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

theorem Erdos679.eventually_log_primeProduct_le :
    ∀ᶠ m : ℕ in atTop, log (primeProduct m : ℝ) ≤
      m * (log m + log (log m) - (3 / 10 : ℝ)) := by sorry
