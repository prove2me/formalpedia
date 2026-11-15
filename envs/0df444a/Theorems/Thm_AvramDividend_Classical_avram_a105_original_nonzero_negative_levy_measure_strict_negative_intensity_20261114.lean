-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a105_original_nonzero_negative_levy_measure_strict_negative_intensity_20261114
-- name    : AvramDividend.Classical.avram_a105_original_nonzero_negative_levy_measure_strict_negative_intensity_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T18:54:10.315975+00:00
-- url     : https://prove2.me/theorems/bb05b87b-3edc-4aca-b516-148ceba71b96
-- title:
--   Spectrally negative original Lévy measure has strictly positive full negative jump intensity whenever nonzero
-- statement:
--   A nonzero Lévy measure of a spectrally negative Lévy process must have positive measure of the entire open negative real half-line because the definition assumes its mass on [0,∞) vanishes. No finite negative activity, process standing assumptions, Brownian coefficient assumption or Poisson jump law is required.
-- source:
--   Source SpectrallyNegativeLevy field ν_Ici: ν(Ici 0)=0; partition of ℝ by Iio 0 and Ici 0, monotonicity/subadditivity of measures; measure univ zero implies measure zero.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a105_original_nonzero_negative_levy_measure_strict_negative_intensity_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hNu : X.ν ≠ 0) :
    0 < X.ν (Iio (0 : ℝ)) := by sorry
