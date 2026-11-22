-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_lsc_zerojump_realTime_increment_gaussian
-- name    : AvramDividend.Classical.avram_lsc_zerojump_realTime_increment_gaussian
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T15:25:26.061949+00:00
-- url     : https://prove2.me/theorems/690bca9c-1a3e-4d54-8a18-5ad43e976417
-- title:
--   Real-time Gaussian increment law for the original zero-jump Avram Lévy source
-- statement:
--   For a zero-jump spectrally negative Lévy process with positive Gaussian coefficient, the centred increment of the original process normalised by its Gaussian coefficient has standard Gaussian law at every nonnegative real start and later real endpoint. This transports the already-proved intrinsic nonnegative-time increment law to the real-time interface used by LevyStochCalc.
-- source:
--   Formal real-time clock bridge from the proved Avram zero-jump Gaussian increment law, UUID 3e682259-c79e-4b1f-a823-124e4ce57182, toward constructing a same-original-space Brownian driver for stopped Itô calculations in fdb9a6a3 and 26396e12.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gbB264_original_zerojump_normalised_increment_exact_gaussian_law
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_lsc_zerojump_realTime_increment_gaussian
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hσ : 0 < X.σ)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    Measure.map (fun ω =>
      ((X.X (Real.toNNReal t) ω - X.X (Real.toNNReal s) ω) -
        (t - s) * X.c) / X.σ) P =
      gaussianReal 0 (Real.toNNReal (t - s)) := by sorry
