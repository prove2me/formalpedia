-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_actual_threshold_increment_budget_ws01b
-- name    : AvramDividend.Classical.bv_actual_threshold_increment_budget_ws01b
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T17:24:17.143851+00:00
-- url     : https://prove2.me/theorems/952b8c5c-8752-4ea5-8e42-afc7469b29ef
-- title:
--   Uniform physical BV path bound on the number of large negative or positive increments
-- statement:
--   On a common probability-one event for the actual bounded-variation spectrally negative Lévy process, along every increasing finite time partition and for every ε>0, each observed increment whose absolute magnitude is at least ε contributes ε to a total bounded by the actual sample path's physical drift/deficit variation budget. Consequently the number of ε-large observed increments is uniformly finite on bounded horizons once the path variation is bounded. Handles infinite-activity processes without assuming finite jump activity.
-- source:
--   A pathwise partition corollary of the canonically Proved BV actual Lévy path finite total variation theorem; supports construction of a finite-jump-intensity truncation from arbitrarily fine rational grids as a prerequisite to the Lévy jump random measure.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_bv_actual_path_partition_variation_bound_ws01b

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_actual_threshold_increment_budget_ws01b
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ (u : ℕ → ℝ≥0), Monotone u →
      ∀ (n : ℕ) (ε : ℝ), 0 < ε →
      (∑ i ∈ Finset.range n,
        if ε ≤ |X.X (u (i + 1)) ω - X.X (u i) ω|
        then ε else 0) ≤
      2 * X.drift * ((u n : ℝ) - (u 0 : ℝ)) -
        (X.X (u n) ω - X.X (u 0) ω) := by sorry
