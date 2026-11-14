-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB225_localtime_density_representation_implies_small_ball_rate
-- name    : AvramDividend.Classical.avram_gbB225_localtime_density_representation_implies_small_ball_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T08:06:55.645208+00:00
-- url     : https://prove2.me/theorems/e59374ab-3e16-49be-9986-ed9158ba8dcc
-- title:
--   A bounded occupation-density representation yields uniform shrinking-band occupation rates
-- statement:
--   For a sample real-valued path on a finite pre-stopping-time horizon, if stopped occupation in every open symmetric spatial band is exactly represented by integrating a spatial density bounded by B, then occupation of the bands of radius 1/(k+1) is at most B times twice their radius.
-- source:
--   Gaussian B208 hard local-time prerequisite reduction. Reuses B176 bounded lintegral and B177 symmetric interval volume without assuming unproved source semimartingale local time.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB225_localtime_density_representation_implies_small_ball_rate
    (f : ℝ → ℝ) (n : ℕ) (ρ y : ℝ)
    (ℓ : ℝ → ℝ≥0∞) (B : ℝ≥0∞)
    (hℓ : ∀ z, ℓ z ≤ B)
    (hOccupation : ∀ ε : ℝ, 0 < ε →
      volume {t : ℝ |
        0 < t ∧ t < (n : ℝ) ∧ t < ρ ∧
        |f t - y| < ε} =
      ∫⁻ z in Set.Ioo (y - ε) (y + ε), ℓ z ∂volume) :
    ∀ k : ℕ,
      volume {t : ℝ |
        0 < t ∧ t < (n : ℝ) ∧ t < ρ ∧
        |f t - y| < (1 : ℝ) / ((k : ℝ) + 1)} ≤
      B * ENNReal.ofReal (2 * ((1 : ℝ) / ((k : ℝ) + 1))) := by sorry
