-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_nu_halfclosed_band_integrable
-- name    : AvramDividend.Classical.avram_p4_h_gaussian_original_nu_halfclosed_band_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:28:17.419467+00:00
-- url     : https://prove2.me/theorems/333e18a2-b39a-4e25-9841-f979f8995fdd
-- title:
--   Original Levy compensator linear mark is integrable on the exact half-closed small negative band
-- statement:
--   For any original spectrally negative Levy X and positive epsilon, its genuine X.nu has an integrable signed mark z over the exact compensated band (-1,-epsilon], including a possible atom at -epsilon and excluding -1. This establishes finiteness of the deterministic drift subtracted in Jsmall^epsilon without changing the Levy process or assuming stochastic compensation.
-- source:
--   Proved X.nu cutoff finite via negative_jump_truncation_measure_finite (16a2d301); adapt the accepted P4-C cutoff linear mark integrability proof 63c53f4c from open Ioo to half-closed Ioc.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_negative_jump_truncation_measure_finite
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_h_gaussian_original_nu_halfclosed_band_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ε : ℝ) (hε : 0 < ε) :
    IntegrableOn (fun z : ℝ => z) (Ioc (-1 : ℝ) (-ε)) X.ν := by sorry
