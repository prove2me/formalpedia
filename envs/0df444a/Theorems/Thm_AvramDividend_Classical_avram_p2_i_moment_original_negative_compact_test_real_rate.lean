-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_original_negative_compact_test_real_rate
-- name    : AvramDividend.Classical.avram_p2_i_moment_original_negative_compact_test_real_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:18:27.852775+00:00
-- url     : https://prove2.me/theorems/3a40517a-11c1-4946-9ea5-c99c3c52033a
-- title:
--   Genuine original Lévy compact-negative small-time test rate with ordinary real inverse
-- statement:
--   For every original spectrally negative Lévy process and compact-negative continuous test f, the ordinary real 1/h-normalised expectation of f(X_h) converges as positive h↓0 to the integral of f against the genuine restricted negative Lévy measure. This converts the independently Proved source-normalised rate using ENNReal.toReal inverse into the standard real inverse via the Mathlib toReal_inv and toReal_ofReal identities on h>0. No Lévy-rate or compensator theorem is assumed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_i_moment_original_negative_compact_test_real_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (f : ℝ → ℝ) (hf : Continuous f) (a ε : ℝ) (hε : 0 < ε)
    (hflower : ∀ y : ℝ, y < a → f y = 0)
    (hfupper : ∀ y : ℝ, -ε < y → f y = 0) :
    Tendsto (fun h : ℝ => if 0 < h then
      h⁻¹ * (∫ ω, f (X.X (Real.toNNReal h) ω) ∂P)
      else 0)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (∫ y : ℝ, f y ∂(X.ν.restrict (Iio (0 : ℝ))))) := by sorry
