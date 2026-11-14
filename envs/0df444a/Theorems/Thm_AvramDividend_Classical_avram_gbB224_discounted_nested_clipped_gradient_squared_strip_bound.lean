-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB224_discounted_nested_clipped_gradient_squared_strip_bound
-- name    : AvramDividend.Classical.avram_gbB224_discounted_nested_clipped_gradient_squared_strip_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T08:03:34.301753+00:00
-- url     : https://prove2.me/theorems/a374c2b7-6f6f-48d3-99ec-9a5d668e411a
-- title:
--   Discounting preserves nested clipped-gradient squared error localisation to boundary strips
-- statement:
--   For nested closed clipping intervals, a derivative bound B of at least one, and any discount factor between zero and one, the square of the difference of the two discounted clipped gradients is at most 4B² times the indicator of the union of the two boundary strips.
-- source:
--   Gaussian B fixed-versus-selected cutoffs bridge: B222 with nonnegative contractive discount, targeting B65 via B220 and fixed-level occupation.

import Mathlib
import Mathlib.Analysis.Calculus.Deriv.Basic
open MeasureTheory Set Filter Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB224_discounted_nested_clipped_gradient_squared_strip_bound
    (w : ℝ → ℝ) (a a' b' b B d : ℝ)
    (ha : a ≤ a') (hab : a' ≤ b') (hb : b' ≤ b)
    (hB : 1 ≤ B)
    (hgrad : ∀ y ∈ Set.Icc a b, |deriv w y| ≤ B)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (y : ℝ) :
    (d * (if y ∈ Set.Icc a b then deriv w y else 1) -
      d * (if y ∈ Set.Icc a' b' then deriv w y else 1))^2 ≤
      4 * B^2 *
        (if y ∈ Set.Icc a a' ∨ y ∈ Set.Icc b' b then (1 : ℝ) else 0) := by sorry
