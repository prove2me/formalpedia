-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_all_cap_generator_residual_le_band_mass
-- name    : AvramDividend.Classical.avram_wave4_05_source_all_cap_generator_residual_le_band_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T17:49:36.558603+00:00
-- url     : https://prove2.me/theorems/3c0d0af2-e2e0-44f9-be20-726fa8dd3ccf
-- title:
--   Unconditional all-cap original source generator upper residual bound by explicit finite Levy band mass
-- statement:
--   Above the finite optimal dividend cap, including zero cap, original compensated generator domain and an unconditional residual upper bound by source drift plus finite strict-ruin-band Levy intensity times the value shortfall minus discount. This is an unconditional explicit analytic bound under source assumptions.
-- source:
--   Unconditional source generator residual bound by overshoot and source-only finite-band mass integral inequality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_05_source_all_cap_generator_residual_le_band_mass {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) (x : ℝ) (hx : (cstar W).toReal < x) : X.GeneratorIntegrable (vcstar W) x ∧ X.generator (vcstar W) x - q * vcstar W x ≤ X.c + (X.ν).real (Ioo (-1 : ℝ) (-x)) * max 0 (1 - vcstar W x) - q * vcstar W x := by sorry
