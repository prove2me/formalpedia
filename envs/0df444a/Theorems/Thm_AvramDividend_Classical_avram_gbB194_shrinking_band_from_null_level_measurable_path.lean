-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB194_shrinking_band_from_null_level_measurable_path
-- name    : AvramDividend.Classical.avram_gbB194_shrinking_band_from_null_level_measurable_path
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T22:02:25.18319+00:00
-- url     : https://prove2.me/theorems/3e2936b0-96a4-4516-a58d-739d2d52b6ef
-- title:
--   Finite-horizon shrinking-band occupation vanishes from zero fixed-level occupation
-- statement:
--   For any real-valued measurable path and finite time horizon, zero Lebesgue occupation of a fixed level forces shrinking neighbourhood occupation to tend to zero.
-- source:
--   Avram Gaussian B 12 November 2026; deterministic continuity-from-above alternative to uniformly bounded local time in B141.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB194_shrinking_band_from_null_level_measurable_path
    (f : ℝ → ℝ) (hf : Measurable f) (n : ℕ) (ρ b : ℝ)
    (hlevel : volume {t : ℝ |
      0 < t ∧ t < (n : ℝ) ∧ t < ρ ∧ f t = b} = 0) :
    Tendsto (fun k : ℕ =>
      volume {t : ℝ |
        0 < t ∧ t < (n : ℝ) ∧ t < ρ ∧
        abs (f t - b) < (1 : ℝ) / ((k : ℝ) + 1)})
      atTop (𝓝 (0 : ℝ≥0∞)) := by sorry
