-- Prove2me | Theorems.Thm_Erdos679_chebyshev_lower_ratio
-- name    : Erdos679.chebyshev_lower_ratio
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:10:50.333236+00:00
-- url     : https://prove2.me/theorems/dad1bba0-37e6-4621-94d5-630e02c03f03
-- title:
--   Erdos679: chebyshev lower ratio
-- statement:
--   The explicit Chebyshev lower bound, normalized at $a x \log x$.
--
--   Source: https://github.com/AItoBit/erdos-679-additive-refutation/blob/4a53d358d1b7ade35d6f696f501c99b4d88c9e4c/Erdos679/Analytic.lean#L65-L95
-- source:
--   https://github.com/AItoBit/erdos-679-additive-refutation/blob/4a53d358d1b7ade35d6f696f501c99b4d88c9e4c/Erdos679/Analytic.lean#L65-L95

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

theorem Erdos679.chebyshev_lower_ratio (a : ℝ) (ha : 0 < a) :
    Tendsto (fun x : ℝ =>
      (((a * x * log x - 1) * log 2 - log (a * x * log x + 2)) /
        log (a * x * log x)) / x) atTop (𝓝 (a * log 2)) := by sorry
