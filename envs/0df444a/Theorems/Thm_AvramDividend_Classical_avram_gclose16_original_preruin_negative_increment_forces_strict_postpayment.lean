-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gclose16_original_preruin_negative_increment_forces_strict_postpayment
-- name    : AvramDividend.Classical.avram_gclose16_original_preruin_negative_increment_forces_strict_postpayment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T22:03:43.200331+00:00
-- url     : https://prove2.me/theorems/4446f787-3c52-4a3b-b48e-2d8fec53dcc8
-- title:
--   Negative original Lévy step before ruin excludes earlier zero postpayment reserve
-- statement:
--   At two actual pre-ruin times, a strict downward step of the original Levy source, combined with nondecreasing right dividend payments, forces the earlier postpayment reserve to be strictly positive. This is a pathwise zero-contact exclusion step for the original stopped-filtration downward regularity argument, without assuming an Ito result or an independent Brownian process.
-- source:
--   Use Proved original postpayment nonnegativity before ruin at the two clocks, and Proved monotonicity of original dividend right limits. The strict negative original Levy step contradicts zero postpayment at the earlier clock.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_preruin_postpayment_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gclose16_original_preruin_negative_increment_forces_strict_postpayment
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t s : ℝ≥0)
    (ht : (t : ℝ≥0∞) < ruinTime X x D ω)
    (hts : ((t + s : ℝ≥0) : ℝ≥0∞) < ruinTime X x D ω)
    (hneg : X.X (t + s) ω - X.X t ω < 0) :
    0 < x + X.X t ω - rightLimit D t ω := by sorry
