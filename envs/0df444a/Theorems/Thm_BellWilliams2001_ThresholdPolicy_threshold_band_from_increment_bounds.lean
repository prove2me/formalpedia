-- Prove2me | Theorems.Thm_BellWilliams2001_ThresholdPolicy_threshold_band_from_increment_bounds
-- name    : BellWilliams2001.ThresholdPolicy.threshold_band_from_increment_bounds
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T05:54:10.795886+00:00
-- url     : https://prove2.me/theorems/8dd1c10c-4a2f-42e1-acbf-499ae5674591
-- title:
--   Threshold excursions stay within a band under deterministic increment bounds
-- statement:
--   Suppose a path starts at zero and has a linear bound on absolute increments with additive error B. Suppose also that its increments have a positive linear lower bound below the threshold and a negative linear upper bound above it, both with additive error B. Then it stays at most 2B above the threshold everywhere and at most 2B below it after its first threshold visit. It must visit the threshold once the lower drift times elapsed time exceeds the threshold plus B.
-- source:
--   Bell and Williams (2001), https://doi.org/10.1214/aoap/1015345343, threshold excursion drift argument in Sections 6–7

import Mathlib

open Set

namespace BellWilliams2001.ThresholdPolicy

theorem threshold_band_from_increment_bounds (q : ℝ → ℝ) (H L K B α : ℝ) (hH : 0 ≤ H) (hL : 0 ≤ L)
    (hK : 0 ≤ K) (hB : 0 ≤ B) (hα : 0 < α) (hZero : q 0 = 0)
    (hAny : ∀ u v, 0 ≤ u → u ≤ v → v ≤ H → |q v-q u| ≤ K*(v-u)+B)
    (hBelow : ∀ u v, 0 ≤ u → u ≤ v → v ≤ H →
      (∀ s ∈ Ioc u v, q s ≤ L) → α*(v-u)-B ≤ q v-q u)
    (hAbove : ∀ u v, 0 ≤ u → u ≤ v → v ≤ H →
      (∀ s ∈ Ioc u v, L < q s) → q v-q u ≤ -α*(v-u)+B) :
    (∀ t ∈ Icc 0 H, q t ≤ L+2*B) ∧
    (∀ t ∈ Icc 0 H, (∃ u ∈ Icc 0 t, L ≤ q u) → L-2*B ≤ q t) ∧
    (∀ t ∈ Icc 0 H, L+B < α*t → ∃ u ∈ Icc 0 t, L ≤ q u) := by sorry

end BellWilliams2001.ThresholdPolicy
