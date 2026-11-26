-- Prove2me | Theorems.Thm_BigEdgeWindowPacking
-- name    : BigEdgeWindowPacking
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:09:23.467158+00:00
-- url     : https://prove2.me/theorems/c69c5eef-dfc6-5028-937b-272c3b04eea2
-- title:
--   Big Edge Window Packing: Big Edge Window Packing
-- statement:
--   A quantitative packing bound for long edges of a monotone breakpoint sequence inside a window:
--   if `s` is monotone on `{0,…,k}` and `a ≤ b`, then the edges `[s (j-1), s j]` with `j ∈ {1,…,k}`
--   that are *fully contained* in `[a,b]` and have length at least `δ > 0` number at most
--   `(b - a)/δ`. Natural-number subtraction is used for `j - 1`.
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/BigEdgeWindowPacking.lean#L10-L70
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/BigEdgeWindowPacking.lean#L10-L70

import Definitions.Def_Tablet_Preamble
import Definitions.Def_Tablet_BigEdgeWindowPacking
set_option autoImplicit false
open Set

theorem BigEdgeWindowPacking (k : ℕ) (s : ℕ → ℝ) (δ a b : ℝ) (hδ : 0 < δ)
    (hmono : MonotoneOn s (Set.Icc 0 k)) (hab : a ≤ b) :
    (((Finset.Icc 1 k).filter
        (fun j => a ≤ s (j - 1) ∧ s j ≤ b ∧ δ ≤ s j - s (j - 1))).card : ℝ) * δ ≤ b - a := by sorry
