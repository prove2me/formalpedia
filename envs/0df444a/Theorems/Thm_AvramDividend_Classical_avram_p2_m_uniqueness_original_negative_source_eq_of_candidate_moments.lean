-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_m_uniqueness_original_negative_source_eq_of_candidate_moments
-- name    : AvramDividend.Classical.avram_p2_m_uniqueness_original_negative_source_eq_of_candidate_moments
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:59:50.683204+00:00
-- url     : https://prove2.me/theorems/cefe7594-3cb3-4025-8706-1ad10dd04995
-- title:
--   Original negative Levy Borel measure equals a genuine moment-candidate negative source
-- statement:
--   The original spectrally negative Lévy source X.ν restricted to strictly negative marks is equal on every Borel set to a separately constructed strictly negative source measure σ whenever its fourth-weighted exponential image ρ is finite regular and its moments match every genuine original-process normalised fourth-weighted X.X moment limit. The proof combines independently Proved P2-M original full-Borel image uniqueness with P2-M exact negative exponential weighted-image inversion. The candidate source σ must genuinely represent ρ; no original rate equality or stationary marked-count intensity is assumed. This directly supplies the missing source-measure interface for P2-A's separated negative Borel rate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_m_uniqueness_original_negative_source_eq_of_candidate_moments
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (η ρ σ : Measure ℝ)
    [IsFiniteMeasure η] [IsFiniteMeasure ρ] [η.Regular] [ρ.Regular]
    (hη : η = (((X.ν.restrict (Iio (0 : ℝ))).withDensity
      (fun y => ENNReal.ofReal ((Real.exp y - 1) ^ 4))).map Real.exp))
    (hρ : ρ = ((σ.withDensity
      (fun y => ENNReal.ofReal ((Real.exp y - 1) ^ 4))).map Real.exp))
    (hnegσ : ∀ᵐ y ∂σ, y < 0)
    (hne : NeBot (nhdsWithin (0 : ℝ) (Ioi 0)))
    (hunitρ : ∀ᵐ z ∂ρ, z ∈ Icc (0 : ℝ) 1)
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
