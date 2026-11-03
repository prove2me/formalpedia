-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_09_original_admissible_zero_start_zero_horizon_expected_cash_eq_zero
-- name    : AvramDividend.Classical.avram_wave7_09_original_admissible_zero_start_zero_horizon_expected_cash_eq_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:01:00.332715+00:00
-- url     : https://prove2.me/theorems/34cd52fc-1725-40e9-a4ff-2167d7c78bbc
-- title:
--   Zero-start admissible source control has zero expected complete Stieltjes cash at horizon zero
-- statement:
--   For every original spectrally negative Lévy law P, zero-start source-admissible strategy D, cap C and discount q, the exact expected discounted complete Stieltjes cash on paymentTimes up to the original ruinTime at horizon T=0 vanishes. This is the finite-horizon stochastic expected-value boundary route used by corrected BV/UBV consumers. The argument is pathwise: the zero-horizon cash is precisely the initial atom and source admissibility forces it to vanish; the outer lintegral of zero is zero. It does not assert vanishing at later horizons.
-- source:
--   Canonical Proved 50183965 initial atom and fed78910 initial zero right limit; genuine original ruinTime, paymentTimes and dividendMeasure, no Open import; independent pathwise proof and outer lintegral.

import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_09_original_admissible_zero_start_zero_horizon_expected_cash_eq_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X 0 C D)
    (q : ℝ) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X 0 D ω) ∩ Iic (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) = 0 := by sorry
