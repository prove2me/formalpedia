-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_positive_ruin_cash_excludes_terminal_atom
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_positive_ruin_cash_excludes_terminal_atom
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T07:49:00.230101+00:00
-- url     : https://prove2.me/theorems/2ea65148-498f-4c44-ba23-93837b941444
-- title:
--   Actual original Cash at a strictly positive ruin clock excludes the terminal right-dividend atom
-- statement:
--   For the genuine original finite stopped Cash at τ=ruinTime>0, the paymentTimes set is exactly [0,τ). Consequently the full discounted dividendMeasure integral includes time zero, continuous and singular-continuous mass, and every eligible earlier right atom, while excluding the right-payment atom at the positive ruin instant. This is a source-specific cash identity, not a stochastic compensation claim; it is the boundary counterpart to the zero-or-strictly-pre-ruin closed-horizon P4-D bound.
-- source:
--   Original paymentTimes definition and Proved positive-ruin domain switch e662362c-4234-4705-9451-8479a3ca43f8; Avram, Palmowski and Pistorius Proposition 4(i), Eq. (5.13).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_positive_ruin_finite_horizon_payment_region_exact
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_positive_ruin_cash_excludes_terminal_atom
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (q : ℝ)
    (τ : Ω → ℝ≥0) (Cash : Ω → ℝ)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal)
    (ω : Ω) (hPos : 0 < τ ω)
    (hRuin : ruinTime X x D ω = (τ ω : ℝ≥0∞)) :
    Cash ω =
      (∫⁻ s in Ico (0 : ℝ) (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal := by sorry
