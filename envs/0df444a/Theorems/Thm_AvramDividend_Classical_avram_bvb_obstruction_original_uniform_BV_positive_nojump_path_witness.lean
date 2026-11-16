-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_original_uniform_BV_positive_nojump_path_witness
-- name    : AvramDividend.Classical.avram_bvb_obstruction_original_uniform_BV_positive_nojump_path_witness
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T07:38:21.343216+00:00
-- url     : https://prove2.me/theorems/2005befa-e791-49e5-9959-877e42c6e9d0
-- title:
--   Full original unit-uniform Standing BV Lévy source with positive-probability exact nojump linear drift path
-- statement:
--   For every original finite horizon T, construct a genuine source process with Standing, bounded variation, finite unit-uniform negative Lévy jumps, zero Gaussian coefficient, unit drift and a positive-probability original sample-path event on which there are no actual negative jump marks and X(t)=t for all t≤T. This is the full original probabilistic witness required by the positive-cap BV pathwise counterexample.
-- source:
--   Directly reuse Proved original uniform Standing BV unit drift source c15b72f3 and Proved original positive-probability nojump linear event 77c05880. The exact event predicate and measure are preserved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_original_uniform_CP_standing_BV_drift_one_source_exists
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_original_positive_probability_nojump_linear_source
open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_bvb_obstruction_original_uniform_BV_positive_nojump_path_witness (T : ℝ≥0) :
    ∃ (P : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
      (𝓕 : Filtration ℝ≥0
        (inferInstance : MeasurableSpace ((ℕ → ℝ) × (ℕ → ℝ))))
      (X : SpectrallyNegativeLevy P 𝓕),
      X.Standing ∧ X.BoundedVariation ∧
      X.ν = (volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0) ∧
      X.ν (Iio (0 : ℝ)) < ⊤ ∧ X.drift = 1 ∧ X.σ = 0 ∧
      0 < P {ω |
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ (X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 T ×ˢ Iio (0 : ℝ)) = 0 ∧
        (∀ t : ℝ≥0, t ≤ T → X.X t ω = (t : ℝ) * X.drift)} := by sorry
