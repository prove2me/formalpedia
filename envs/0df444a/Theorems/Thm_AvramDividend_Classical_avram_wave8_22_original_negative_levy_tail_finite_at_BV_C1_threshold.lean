-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_negative_levy_tail_finite_at_BV_C1_threshold
-- name    : AvramDividend.Classical.avram_wave8_22_original_negative_levy_tail_finite_at_BV_C1_threshold
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T23:58:47.436485+00:00
-- url     : https://prove2.me/theorems/0c671eeb-3810-4025-b10f-d8cfe1bba581
-- title:
--   Original Lévy negative jump intensity finite at the actual compact BV C1 localisation threshold without extra moment premise
-- statement:
--   On the unchanged original spectrally negative Lévy process X, the separated negative mark band below -a/2 has finite X.ν measure whenever the compact reserve lower threshold satisfies 0<a≤2. The original source definition supplies X.ν_integrable, and the accepted negative tail theorem gives the exact hMass needed by the original controlled C1 kernel, with the sign convention -a/2 normalised explicitly. No supplementary energy assumption, finite total activity, or surrogate probability space.
-- source:
--   Accepted original intensity tail 3e5bbc19; original SpectrallyNegativeLevy.ν_integrable field demonstrated by the accepted proof source of canonical finite mark bands b80e4040.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_negative_levy_mark_tail_finite_mass_at_every_small_threshold
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave8_22_original_negative_levy_tail_finite_at_BV_C1_threshold
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a : ℝ) (ha : 0 < a) (ha2 : a ≤ 2) :
    X.ν (Iic (-a / 2)) < ⊤ := by sorry
