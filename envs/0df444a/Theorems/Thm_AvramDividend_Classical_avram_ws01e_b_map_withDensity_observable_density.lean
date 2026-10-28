-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_map_withDensity_observable_density
-- name    : AvramDividend.Classical.avram_ws01e_b_map_withDensity_observable_density
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T08:01:24.207867+00:00
-- url     : https://prove2.me/theorems/da772096-f67b-4aa8-b3b1-33f148819b7f
-- title:
--   Pushforward of an observation-dependent density tilt equals density tilt of its pushforward law
-- statement:
--   For any measure μ, measurable observation map F and nonnegative measurable reward/density w of the observed F-value, the pushforward of the source law weighted by w(F(x)) equals the pushforward law weighted by w. This elementary exact measure identity links a finite-horizon Esscher density expressed in terms of a path's terminal increment sum to the tilted joint law of the finite-mesh increment vector. It does not assume an Esscher infinite-horizon process or Wiener–Hopf identity.
-- source:
--   Pinned Mathlib Measure.ext, Measure.map_apply, withDensity_apply, lintegral_indicator, and lintegral_map.

import Mathlib

open MeasureTheory Set
open scoped ENNReal

/-- Pushing a law forward through F commutes with a density depending
only on the observed F-value. -/

theorem AvramDividend.Classical.avram_ws01e_b_map_withDensity_observable_density
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (F : α → β) (hF : Measurable F)
    (w : β → ℝ≥0∞) (hw : Measurable w) :
    Measure.map F (μ.withDensity (w ∘ F)) =
      (Measure.map F μ).withDensity w := by sorry
