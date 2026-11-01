-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_03_source_postPayment_discounted_exponential_joint_time_path_measurable
-- name    : AvramDividend.Classical.avram_wave4_03_source_postPayment_discounted_exponential_joint_time_path_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T13:47:45.583982+00:00
-- url     : https://prove2.me/theorems/30c00aaa-761d-4772-b41f-9cc5f0238475
-- title:
--   Actual same-path controlled Lévy discounted exponential integrand is jointly measurable in time and probability
-- statement:
--   For the actual original Lévy X and the same admissible left-continuous adapted D, the postpayment discounted exponential is jointly measurable in (t,ω). It follows from the original source postpayment reserve right continuity and adaptedness, plus the proved joint evaluation theorem for right-continuous measurable sections. It ensures stochastic/temporal integration measurability without replacing X by an independent copy.
-- source:
--   Proved postPaymentReserve_cadlag_adapted a2763475 and rightContinuous_measurable_sections_joint_evaluation 8aafec11

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_cadlag_adapted
import Theorems.Thm_AvramDividend_Classical_rightContinuous_measurable_sections_joint_evaluation

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.avram_wave4_03_source_postPayment_discounted_exponential_joint_time_path_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (θ q : ℝ) :
    Measurable (fun z : ℝ≥0 × Ω =>
      Real.exp (θ * (x + X.X z.1 z.2 - rightLimit D z.1 z.2) -
        (z.1 : ℝ) * q)) := by sorry
