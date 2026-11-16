-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_original_uniform_unit_drift_forces_c_half
-- name    : AvramDividend.Classical.avram_bvb_obstruction_original_uniform_unit_drift_forces_c_half
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T09:46:05.69388+00:00
-- url     : https://prove2.me/theorems/d5be8501-9514-491c-8df4-61a4b3842bee
-- title:
--   Original uniform-negative Lévy source with unit BV drift necessarily has Lévy coefficient one half
-- statement:
--   For any original spectrally negative Lévy process with exact negative-uniform unit mark measure and unit bounded-variation drift, the original small-jump compensated Lévy coefficient c is exactly 1/2. This completes the source parameter bridge from the Proved standing BV Poisson witness to the Proved positive-cap HJB candidate.
-- source:
--   Unfold original BV drift, substitute the exact uniform mark measure, rearrange c=1+first moment and reuse Proved exact uniform compound-Poisson coefficient identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_bvb_obstruction_original_uniform_unit_drift_forces_c_half
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = (volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0))
    (hDrift : X.drift = 1) :
    X.c = 1 / 2 := by sorry
