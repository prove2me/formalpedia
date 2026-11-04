-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_cash_L1
-- name    : AvramDividend.Classical.avram_p3_bv_original_strict_cash_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:16:00.269511+00:00
-- url     : https://prove2.me/theorems/67a9c5bf-abbc-40e3-9ccc-a96995d00889
-- title:
--   Exact original stopped dividend cash strictly before the horizon is integrable
-- statement:
--   For the genuine original spectrally negative Lévy process and arbitrary cap-admissible dividend strategy, the exact discounted payout strictly before T is L1 under original P for q nonnegative. The source full cash is L1 and pointwise finite; the strictly restricted cash is measurable and dominated by full cash by the exact split into strict times and the T right-payment atom. Includes the time-zero atom and all diffuse payments, excludes the horizon atom.
-- source:
--   Accepted original full cash L1 f97e4695; pathwise real/ENNReal equality a5c80ef7; exact horizon split 925b8293; new strict-cash kernel measurability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_bv_original_strict_cash_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ) (hT : 0 ≤ T) :
    Integrable (fun ω : Ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal) P := by sorry
