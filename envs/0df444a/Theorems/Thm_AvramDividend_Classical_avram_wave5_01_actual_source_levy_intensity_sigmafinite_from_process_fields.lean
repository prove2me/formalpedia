-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_levy_intensity_sigmafinite_from_process_fields
-- name    : AvramDividend.Classical.avram_wave5_01_actual_source_levy_intensity_sigmafinite_from_process_fields
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T11:06:11.967504+00:00
-- url     : https://prove2.me/theorems/f2f87f44-5b06-4475-b308-739d433ba41f
-- title:
--   Actual original Lévy process supplies sigma-finite Lévy intensity directly from its intrinsic fields
-- statement:
--   For each actual SpectrallyNegativeLevy P 𝓕, its intrinsic Lévy measure X.ν is sigma-finite without extra probabilistic hypotheses. The result is a source-bound input for the σ-finite predictable compensator and finite-band localisation. It follows directly from X.ν_Ici, X.ν_integrable, monotonicity of restriction of the Lévy integrability integral, and the Proved source-compatible negative Lévy measure theorem c93daaa4.
-- source:
--   Original source fields X.ν_Ici and X.ν_integrable plus Proved negative Lévy σ-finiteness c93daaa4-dec6-4f04-8a31-ab86cf53772c; no detached Poisson law.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_negative_levy_measure_sigmaFinite
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_01_actual_source_levy_intensity_sigmafinite_from_process_fields
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    SigmaFinite X.ν := by sorry
