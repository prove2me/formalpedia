-- Prove2me | Theorems.Thm_AvramDividend_Classical_zero_cap_dividendMeasure_restrict_paymentTimes_eq_of_pos_ruin
-- name    : AvramDividend.Classical.zero_cap_dividendMeasure_restrict_paymentTimes_eq_of_pos_ruin
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T14:14:05.383722+00:00
-- url     : https://prove2.me/theorems/0121d7d1-c7cf-44d7-8542-3167e9713bca
-- title:
--   A zero-capped dividend strategy and the zero barrier have equal Stieltjes measures on full pre-ruin payment times
-- statement:
--   On every sample path with strictly positive possibly infinite ruin time, the actual Stieltjes dividend measure of any zero-capped admissible strategy and the zero-barrier strategy agree after restriction to [0,σ), including the time-zero convention and all continuous payments, while excluding any atom at a positive ruin time. This assembles the proved finite pre-ruin restrictions with the proved countable rational exhaustion and a new countable directed-measure union lemma.
-- source:
--   Exact Prove2Me paymentTimes/ruinTime/dividendMeasure; Avram–Palmowski–Pistorius (2007), §2-3; pinned Mathlib directed measure-restriction identity.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_eq_iUnion_strict_rational_prefixes
import Theorems.Thm_AvramDividend_Classical_measure_restrict_iUnion_eq_of_countable_directed_prefix
import Theorems.Thm_AvramDividend_Classical_zero_cap_dividendMeasure_restrict_Ico_eq

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.zero_cap_dividendMeasure_restrict_paymentTimes_eq_of_pos_ruin
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X 0 0 D)
    (ω : Ω) (hσ : 0 < ruinTime X 0 D ω) :
    (dividendMeasure D ω).restrict (paymentTimes (ruinTime X 0 D ω)) =
    (dividendMeasure (barrierStrategy X 0 0) ω).restrict
      (paymentTimes (ruinTime X 0 D ω)) := by sorry
