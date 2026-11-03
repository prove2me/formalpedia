-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_real_toReal_cash_mean_eq_signed_stieltjes_mean
-- name    : AvramDividend.Classical.avram_wave7_03_original_real_toReal_cash_mean_eq_signed_stieltjes_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T13:30:34.983913+00:00
-- url     : https://prove2.me/theorems/071f73a3-dc83-47ce-8fae-5b22f5d87a8e
-- title:
--   Original real expectation of ENNReal cash toReal equals genuine signed real stopped Stieltjes expectation
-- statement:
--   Under original capped admissible dividends, q>=0, real horizon T>=0, the real outer integral of the original ruin-stopped ENNReal discounted cash converted pathwise with ENNReal.toReal equals the real outer integral of the actual signed discounted Stieltjes reward on exactly paymentTimes(ruinTime) cap Iic T with exactly dividendMeasure D omega. The pathwise same-measure finite-mass equality a5c80ef7 and nonnegativity of exp justify converting ofReal back to real. This provides a typed equality between the common stochastic budget expression and the genuine signed Stieltjes expectation; full integrability is available from accepted original cash L1 and W7-03 real L1. Includes initial rightLimit atom and all diffuse and interior jump payments.
-- source:
--   Accepted W7-03 original finite-horizon pathwise same-domain equality a5c80ef7; Real.coe_toNNReal, integral_nonneg and ENNReal.toReal_ofReal.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_full_ruin_finite_horizon_real_ennreal_eq
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_real_toReal_cash_mean_eq_signed_stieltjes_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ) (hT : 0 ≤ T) :
    (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal ∂P) =
    (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by sorry
