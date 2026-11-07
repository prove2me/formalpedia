-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_redux14_original_bv_levy_exp_deficit_integrable
-- name    : AvramDividend.Classical.avram_redux14_original_bv_levy_exp_deficit_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T10:56:02.103304+00:00
-- url     : https://prove2.me/theorems/684100d2-ff05-4a7d-a133-477d32e05051
-- title:
--   Original BV Lévy negative exponential deficit is integrable
-- statement:
--   For every bounded-variation spectrally negative Lévy process, the deficit of the negative-jump exponential transform is absolutely integrable under the Lévy measure on negative jumps. The pointwise estimate 0 ≤ 1 - exp(y) ≤ min(1,|y|) for y<0 and the previously Proved bounded-variation min(1,|y|) integrability theorem give the result.
-- source:
--   Original BV Lévy measure, deterministic analytic integrability required for monotone set-integral convergence at zero cutoff in Redux13.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_redux14_original_bv_levy_exp_deficit_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    IntegrableOn (fun y : ℝ => 1 - Real.exp y) (Iio (0 : ℝ)) X.ν := by sorry
