-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_e0_czero_singular_standing
-- name    : AvramDividend.Classical.avram_e0_czero_singular_standing
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T17:51:03.664481+00:00
-- url     : https://prove2.me/theorems/12e21306-f751-4d7f-a151-6cbcfa689cb4
-- title:
--   Singular zero-coefficient spectrally negative model satisfies Standing once its unit increment is integrable
-- statement:
--   For the original Avram Levy model with zero canonical triplet coefficient and singular negative-jump density, finite expectation of the unit-time process implies Standing. The signed Levy moment gives positive physical drift and excludes the zero Levy measure, while the verified density is absolutely continuous.
-- source:
--   Necessary original Standing discharge for e0b94d7f-cb1e-450a-8f04-b2e732af5dbe countermodel.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gen15_singular_density_restricted_signed_moment_neg_two
import Theorems.Thm_AvramDividend_Classical_avram_e0_singular_czero_drift_eq_two
import Theorems.Thm_AvramDividend_Classical_avram_e0_standing_of_positive_drift_singular_density
open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_e0_czero_singular_standing
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hc : X.c = 0)
    (hν : X.ν = volume.withDensity (fun z : ℝ =>
      if z ∈ Ioo (-1 : ℝ) 0
      then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0))
    (hint : Integrable (X.X 1) P) : X.Standing := by sorry
