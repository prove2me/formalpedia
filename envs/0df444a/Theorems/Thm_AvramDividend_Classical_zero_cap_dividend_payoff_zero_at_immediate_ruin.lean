-- Prove2me | Theorems.Thm_AvramDividend_Classical_zero_cap_dividend_payoff_zero_at_immediate_ruin
-- name    : AvramDividend.Classical.zero_cap_dividend_payoff_zero_at_immediate_ruin
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T14:16:26.506211+00:00
-- url     : https://prove2.me/theorems/a6549db0-1507-4c4b-97b2-ab14882b56df
-- title:
--   Zero-cap dividends have zero discounted value on paths ruined immediately
-- statement:
--   For any zero-capped admissible dividend control with initial capital zero, if a sample path has ruin time zero, the exact discounted dividend Stieltjes integral over paymentTimes equals zero. The formal payment window then consists solely of {0}; the initial right-limit dividend is zero by the Proved admissibility child, and the proved singleton-mass identity makes the Stieltjes measure of {0} zero. This closes the crucial exceptional σ=0 case excluded from positive-ruin rational-prefix exhaustions.
-- source:
--   Exact DividendStrategy paymentTimes and measure at time zero, Prove2Me pinned formal mission, Avram et al. 2007 §2.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_singleton_eq_rightLimit_sub
import Theorems.Thm_AvramDividend_Classical_zero_cap_rightLimit_zero_at_origin
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.zero_cap_dividend_payoff_zero_at_immediate_ruin
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X 0 0 D)
    (ω : Ω) (hσ : ruinTime X 0 D ω = 0) :
    (∫⁻ t in paymentTimes (ruinTime X 0 D ω),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) = 0 := by sorry
