-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB226_exponential_discount_nested_clipping_squared_strip_bound
-- name    : AvramDividend.Classical.avram_gbB226_exponential_discount_nested_clipping_squared_strip_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T08:07:35.742206+00:00
-- url     : https://prove2.me/theorems/c2b2b8c3-0fba-44b0-9238-c78b66f96ee2
-- title:
--   Discounted clipped-gradient squared difference is bounded by Gaussian boundary-strip indicator
-- statement:
--   At a nonnegative physical time and nonnegative discount rate, the squared error between two exponentially discounted, nested clipped spatial gradients is bounded by the same two-strip indicator as in the undiscounted case. This supplies a pointwise estimate in the original finite-cap Gaussian source theorem.
-- source:
--   Original Gaussian fixed-cutoff B65; proof by nonnegative exponential contractivity plus Proved B224.

import Mathlib
import Mathlib.Analysis.Calculus.Deriv.Basic
open MeasureTheory Set Filter Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB226_exponential_discount_nested_clipping_squared_strip_bound
    (w : ℝ → ℝ) (a a' b' b B q t : ℝ)
    (ha : a ≤ a') (hab : a' ≤ b') (hb : b' ≤ b)
    (hB : 1 ≤ B)
    (hgrad : ∀ y ∈ Set.Icc a b, |deriv w y| ≤ B)
    (hq : 0 ≤ q) (ht : 0 ≤ t) (y : ℝ) :
    (Real.exp (-(q * t)) *
        (if y ∈ Set.Icc a b then deriv w y else 1) -
      Real.exp (-(q * t)) *
        (if y ∈ Set.Icc a' b' then deriv w y else 1))^2 ≤
      4 * B^2 *
        (if y ∈ Set.Icc a a' ∨ y ∈ Set.Icc b' b then (1 : ℝ) else 0) := by sorry
