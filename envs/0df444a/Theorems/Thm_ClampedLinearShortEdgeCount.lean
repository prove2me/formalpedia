-- Prove2me | Theorems.Thm_ClampedLinearShortEdgeCount
-- name    : ClampedLinearShortEdgeCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:07:21.486989+00:00
-- url     : https://prove2.me/theorems/e727cd47-098b-456b-bc4a-51a2c7c069f5
-- title:
--   Clamped Linear Short Edge Count: Clamped Linear Short Edge Count
-- statement:
--   The linear counting clause of a `(δ,ε,n)`-curve extends from window pairs `(a,b)` constrained
--   by `0 ≤ a ≤ b ≤ L` to *arbitrary* real pairs `(a,b)` subject only to the gap bound
--   `b - a ≤ 2ε⁻¹δ`. The point is that a breakpoint sequence `s` running monotonically inside `[0,L]`
--   cannot see the part of a window that sticks out of `[0,L]`: replacing `(a,b)` by the clamped pair
--   `(max a 0, min b L)` only enlarges the counted set while shrinking the gap, so the clause applied
--   at the clamped pair dominates the count at the original pair. Vacuously true when the counted set
--   is empty, which is the only case where the clamped pair can fail to be ordered.
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/ClampedLinearShortEdgeCount.lean#L13-L46
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/ClampedLinearShortEdgeCount.lean#L13-L46

import Definitions.Def_Tablet_Preamble
import Definitions.Def_Tablet_ClampedLinearShortEdgeCount
set_option autoImplicit false
open Set

theorem ClampedLinearShortEdgeCount (k n : ℕ) (δ ε L : ℝ) (s : ℕ → ℝ)
    (hmono : MonotoneOn s (Set.Icc 0 k))
    (hlow : ∀ j : ℕ, j ≤ k → 0 ≤ s j) (hhigh : ∀ j : ℕ, j ≤ k → s j ≤ L)
    (hlin : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ L → b - a ≤ 2 * ε⁻¹ * δ →
      ((Finset.Icc 1 k).filter
        (fun j => a ≤ s (j - 1) ∧ s j ≤ b ∧ s j - s (j - 1) < δ)).card ≤ n)
    (a b : ℝ) (hab : b - a ≤ 2 * ε⁻¹ * δ) :
    ((Finset.Icc 1 k).filter
      (fun j => a ≤ s (j - 1) ∧ s j ≤ b ∧ s j - s (j - 1) < δ)).card ≤ n := by sorry
