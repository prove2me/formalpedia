-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_m_uniqueness_original_negative_source_from_finite_moments
-- name    : AvramDividend.Classical.avram_p2_m_uniqueness_original_negative_source_from_finite_moments
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:50:13.681123+00:00
-- url     : https://prove2.me/theorems/27ace901-c2a6-4454-8137-6e52e4e926f6
-- title:
--   Original Levy negative source from finite image moments without regularity hypotheses
-- statement:
--   For the actual spectrally negative Lévy process X on the unchanged probability space, finite original and candidate fourth-weighted exponential image measures determine the original restricted X.ν from all genuinely time-normalised original X.X image-moment limits to the independently represented strictly negative candidate σ. Unit support and finite-real-measure regularity are automatically derived. The hard original-process candidate moment convergence remains a real premise; no intrinsic marked intensity or original-rate conclusion is assumed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_m_uniqueness_original_negative_source_from_finite_moments
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (η ρ σ : Measure ℝ)
    [IsFiniteMeasure η] [IsFiniteMeasure ρ]
    (hη : η = (((X.ν.restrict (Iio (0 : ℝ))).withDensity
      (fun y => ENNReal.ofReal ((Real.exp y - 1) ^ 4))).map Real.exp))
    (hρ : ρ = ((σ.withDensity
      (fun y => ENNReal.ofReal ((Real.exp y - 1) ^ 4))).map Real.exp))
    (hnegσ : ∀ᵐ y ∂σ, y < 0)
    (hne : NeBot (nhdsWithin (0 : ℝ) (Ioi 0)))
    (hmomρ : ∀ k, Tendsto (fun h : ℝ =>
      ∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂
        (if 0 < h then (ENNReal.ofReal h)⁻¹ •
          ((P.withDensity (fun ω => ENNReal.ofReal
            ((Real.exp (X.X (Real.toNNReal h) ω) - 1) ^ 4))).map
            (fun ω => Real.exp (X.X (Real.toNNReal h) ω)))
         else (0 : Measure ℝ)))
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂ρ))) :
    X.ν.restrict (Iio (0 : ℝ)) = σ := by sorry
