-- Prove2me | Theorems.Thm_AvramDividend_Classical_zero_cap_dividendMeasure_Ico_eq_barrier_before_ruin
-- name    : AvramDividend.Classical.zero_cap_dividendMeasure_Ico_eq_barrier_before_ruin
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T12:40:56.984512+00:00
-- url     : https://prove2.me/theorems/eb4ef403-6426-49c7-8c46-c532e8682ab0
-- title:
--   Zero-cap dividend measures agree on every strict pre-ruin half-open interval
-- statement:
--   For any zero-cap admissible strategy and any two nonnegative real-times a≤b with 0<b strictly before its ruin, the precise dividend Stieltjes measures of the strategy and zero-barrier reflection agree on the interval [a,b). This includes both continuous payments and right-limit atoms, and follows from the published half-open interval dividend increment formula and the proved zero-cap pathwise barrier equality.
-- source:
--   Exact Prove2Me dividend strategy/Stieltjes definitions, supporting the degenerate C=0 verification in Avram et al. (2007), Theorem 2(i).

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ico_eq_dividend_increment
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_isDividendStrategy_nonnegative_barrier
import Theorems.Thm_AvramDividend_Classical_zero_cap_barrier_eq_control_before_ruin
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.zero_cap_dividendMeasure_Ico_eq_barrier_before_ruin
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X 0 0 D)
    (ω : Ω) (a b : ℝ≥0) (hab : a ≤ b) (hb : 0 < b)
    (hbr : (b : ℝ≥0∞) < ruinTime X 0 D ω) :
    dividendMeasure D ω (Ico (a : ℝ) (b : ℝ)) =
      dividendMeasure (barrierStrategy X 0 0) ω
        (Ico (a : ℝ) (b : ℝ)) := by sorry
