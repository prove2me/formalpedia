-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_original_levy_weighted_log_test_tendsto
-- name    : AvramDividend.Classical.avram_p2_i_moment_original_levy_weighted_log_test_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:01:48.571817+00:00
-- url     : https://prove2.me/theorems/bc4cc2b9-c295-4e57-b2b9-ae91a8b8eaad
-- title:
--   Actual original Lévy weighted logarithmic compact tests converge to the negative Lévy-image limit
-- statement:
--   For any genuine original spectrally negative Lévy process and every continuous test supported strictly inside a compact negative real-mark band, the time-normalised fourth-weighted exponential-image integral of f(log z)/(z-1)^4 converges as h decreases to zero to its integral against the fourth-weighted original negative Lévy measure image. Directly assembles Proved original normalized source moments, Proved exact support and finiteness helpers, and the P2-I positive-band moment-to-continuous-test theorem. It does not import P2-K's Open compact-test theorem and does not presuppose the desired jump intensity or rate identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_i_moment_original_levy_weighted_log_test_tendsto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (f : ℝ → ℝ) (hf : Continuous f) (a ε : ℝ) (hε : 0 < ε)
    (hflower : ∀ y : ℝ, y < a → f y = 0)
    (hfupper : ∀ y : ℝ, -ε < y → f y = 0) :
    Tendsto (fun h : ℝ => ∫ z : ℝ, f (Real.log z) / (z - 1) ^ 4 ∂
      (if 0 < h then (ENNReal.ofReal h)⁻¹ •
        ((P.withDensity (fun ω => ENNReal.ofReal
          ((Real.exp (X.X (Real.toNNReal h) ω) - 1) ^ 4))).map
          (fun ω => Real.exp (X.X (Real.toNNReal h) ω)))
       else (0 : Measure ℝ)))
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (∫ z : ℝ, f (Real.log z) / (z - 1) ^ 4 ∂
        (((X.ν.restrict (Iio (0 : ℝ))).withDensity
          (fun y => ENNReal.ofReal ((Real.exp y - 1) ^ 4))).map Real.exp))) := by sorry
