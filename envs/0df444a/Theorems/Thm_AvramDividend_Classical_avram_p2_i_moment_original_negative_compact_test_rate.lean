-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_original_negative_compact_test_rate
-- name    : AvramDividend.Classical.avram_p2_i_moment_original_negative_compact_test_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:12:24.883676+00:00
-- url     : https://prove2.me/theorems/49b243b0-ce12-4167-b66c-04f029a84199
-- title:
--   Original spectrally negative Lévy compact-negative test small-time rate from genuine weighted moments
-- statement:
--   For every original spectrally negative Lévy process and continuous test supported strictly in a negative real band, the inverse-positive-time normalised original expectation of f(X_h) converges as h↓0 to the integral of f against the actual restricted negative Lévy measure. The proof combines independently Proved original-process weighted-log-image compact-test convergence with a source-exact Bochner measure-change identity for the fourth power weight. No desired jump-intensity or compensator theorem is assumed. The normalisation is expressed by the exact ENNReal.toReal inverse, equal to real h⁻¹ for h>0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_i_moment_original_negative_compact_test_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (f : ℝ → ℝ) (hf : Continuous f) (a ε : ℝ) (hε : 0 < ε)
    (hflower : ∀ y : ℝ, y < a → f y = 0)
    (hfupper : ∀ y : ℝ, -ε < y → f y = 0) :
    Tendsto (fun h : ℝ => if 0 < h then
      ((ENNReal.ofReal h)⁻¹).toReal *
        (∫ ω, f (X.X (Real.toNNReal h) ω) ∂P)
      else 0)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (∫ y : ℝ, f y ∂(X.ν.restrict (Iio (0 : ℝ))))) := by sorry
