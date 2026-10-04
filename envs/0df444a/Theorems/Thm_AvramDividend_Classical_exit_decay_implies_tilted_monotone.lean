-- Prove2me | Theorems.Thm_AvramDividend_Classical_exit_decay_implies_tilted_monotone
-- name    : AvramDividend.Classical.exit_decay_implies_tilted_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-03T13:57:55.828482+00:00
-- url     : https://prove2.me/theorems/d9758234-eeec-4f19-867c-ee046cd51885
-- title:
--   First passage exponential bound implies tilted scale-function monotonicity
-- statement:
--   For any real function W, if W(x) ≤ exp(-φ(y-x)) W(y) whenever 0<x≤y, then exp(-φx)W(x) is nondecreasing for x>0. This elementary consequence can be used to translate two-sided and one-sided first passage comparisons into the Esscher-monotonicity bridge.
-- source:
--   Generic consequence of the two-sided-exit formula and upward passage Laplace transform, as in Kuznetsov Kyprianou Rivero, Theory of Scale Functions (2012), fluctuation identities.

import Mathlib
open Set

namespace AvramDividend.Classical

/-- A first-passage-type exponential upper bound on scale-function ratios
implies monotonicity of the Esscher-normalised function. -/
theorem exit_decay_implies_tilted_monotone (W : ℝ → ℝ) (φ : ℝ)
    (hbound : ∀ x y : ℝ, 0 < x → x ≤ y →
       W x ≤ Real.exp (-φ * (y - x)) * W y) :
    MonotoneOn (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0) := by
  sorry

end AvramDividend.Classical
