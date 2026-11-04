-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_normalised_increment_mgf_matches_gaussian
-- name    : AvramDividend.Classical.avram_p4_a_gaussian_original_normalised_increment_mgf_matches_gaussian
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T00:15:42.396237+00:00
-- url     : https://prove2.me/theorems/8b2d462d-9781-43c8-88cd-4b2632e06e76
-- title:
--   Original normalised zero-jump Gaussian deterministic increments match Gaussian MGF
-- statement:
--   For original same-volatility Levy sources X,Y where Y has zero jump measure and σ>0, the MGF at every nonnegative parameter of each centred normalised increment over [s,t] equals the real Gaussian MGF with variance t−s.
-- source:
--   Proved fixed-time P4-A normalised Gaussian MGF and original stationaryIncrements; Mathlib mgf_congr_identDistrib.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_normalised_mgf_matches_gaussian_real

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_a_gaussian_original_normalised_increment_mgf_matches_gaussian
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X Y : SpectrallyNegativeLevy P 𝓕)
    (hν : Y.ν = 0) (hσeq : Y.σ = X.σ) (hσ : 0 < X.σ)
    (s t : ℝ≥0) (hst : s ≤ t) (θ : ℝ) (hθ : 0 ≤ θ) :
    ProbabilityTheory.mgf
      (fun ω => ((Y.X t ω - Y.X s ω) - ((t - s : ℝ≥0) : ℝ) * Y.c) / X.σ)
      P θ =
        ProbabilityTheory.mgf id
          (ProbabilityTheory.gaussianReal 0 (t - s)) θ := by sorry
