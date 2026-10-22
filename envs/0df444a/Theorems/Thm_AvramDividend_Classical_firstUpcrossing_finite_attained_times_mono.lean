-- Prove2me | Theorems.Thm_AvramDividend_Classical_firstUpcrossing_finite_attained_times_mono
-- name    : AvramDividend.Classical.firstUpcrossing_finite_attained_times_mono
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T09:28:45.401479+00:00
-- url     : https://prove2.me/theorems/1696e497-c8a6-476f-a427-8dec214e0c4c
-- title:
--   Finite real first-record upcrossing times inherit monotonicity from the original extended-real clock
-- statement:
--   For the original spectrally negative Lévy process and two levels b≤c, suppose the extended-real first strict upward passage infima equal the embeddings of finite nonnegative real times u and v respectively. Then u≤v as real times. This is the exact cast-to-finite-times corollary of the nonnegative extended-real first-upcrossing threshold monotonicity theorem. It removes the artificial extra time-order assumptions from later two-cell and finite-grid record-level Stieltjes dividend estimates.
-- source:
--   Dependency-gated firstUpcrossing_threshold_iInf_mono target 4c7a39ae-f280-47fb-91ab-817b588dc9b2, candidate 12534, plus exact NNReal/ENNReal order-preserving casts.

import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_threshold_iInf_mono

open MeasureTheory Set
open scoped NNReal ENNReal Classical
open AvramDividend.Classical

theorem AvramDividend.Classical.firstUpcrossing_finite_attained_times_mono
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (b c : ℝ) (hbc : b ≤ c)
    (u v : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (r : ℝ≥0) (_ : b < X.X r ω), (r : ℝ≥0∞)))
    (hv : (v : ℝ≥0∞) =
      (⨅ (r : ℝ≥0) (_ : c < X.X r ω), (r : ℝ≥0∞))) : (u : ℝ) ≤ (v : ℝ) := by sorry
