-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn13_original_finite_discounted_stopped_endpoint_atom
-- name    : AvramDividend.Classical.avram_bv_env3_turn13_original_finite_discounted_stopped_endpoint_atom
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T23:00:08.366717+00:00
-- url     : https://prove2.me/theorems/f1f76c6b-0b9b-40cc-93c6-42d506f2b54b
-- title:
--   Finite original discounted stopped singleton endpoint payment mass
-- statement:
--   The discounted dividendMeasure of the original admissible strategy assigns finite mass to the surviving payment-masked endpoint singleton at any τ≤T. The exact time-zero and horizon atom are retained, with finiteness from the original rightLimit D T equality.
-- source:
--   Specialise accepted original measure finiteness source c4e50d93 to the endpoint singleton, using its imported source facts paymentTimes_membership_to_nNReal_active, paymentTimes_measurable, avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit. Feeds original contact-tail toReal continuity, no additional finite endpoint assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_membership_to_nNReal_active
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_env3_turn13_original_finite_discounted_stopped_endpoint_atom
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (σ : ℝ≥0∞) (τ T : ℝ≥0) (hτT : τ ≤ T)
    (q : ℝ) (hq : 0 ≤ q) :
    (∫⁻ s in paymentTimes σ ∩ ({(τ : ℝ)} : Set ℝ),
      ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)) < ⊤ := by sorry
