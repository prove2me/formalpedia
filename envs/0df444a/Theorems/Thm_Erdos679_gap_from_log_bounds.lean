-- Prove2me | Theorems.Thm_Erdos679_gap_from_log_bounds
-- name    : Erdos679.gap_from_log_bounds
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T15:01:15.65288+00:00
-- url     : https://prove2.me/theorems/c15e11d6-3f8b-4009-92a3-146dec6339b9
-- title:
--   Erdos679: gap from log bounds
-- statement:
--   A fixed saving in a logarithmic upper bound forces an unbounded additive gap.
--
--   Source: https://github.com/AItoBit/erdos-679-additive-refutation/blob/4a53d358d1b7ade35d6f696f501c99b4d88c9e4c/Erdos679/Gap.lean#L51-L110
-- source:
--   https://github.com/AItoBit/erdos-679-additive-refutation/blob/4a53d358d1b7ade35d6f696f501c99b4d88c9e4c/Erdos679/Gap.lean#L51-L110

module
public import Mathlib.Analysis.SpecialFunctions.Log.Monotone
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Definitions.Def_Erdos679_Gap
set_option autoImplicit false
@[expose] public section
public section
open Filter Real
open scoped Topology
open Erdos679

theorem Erdos679.gap_from_log_bounds (θ : ℕ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hupper : ∀ᶠ m : ℕ in atTop,
      θ m ≤ m * (log m + log (log m) - δ))
    (hlower : ∀ᶠ m : ℕ in atTop, m * (log m - 2) < θ m) (C : ℝ) :
    ∀ᶠ m : ℕ in atTop, θ m / log (θ m) + C < m := by sorry
