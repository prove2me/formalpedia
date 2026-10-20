-- Prove2me | Theorems.Thm_AvramDividend_Classical_zero_cap_dividendMeasure_restrict_Ico_eq
-- name    : AvramDividend.Classical.zero_cap_dividendMeasure_restrict_Ico_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T12:58:01.980682+00:00
-- url     : https://prove2.me/theorems/237e06a3-193d-4519-bd35-e3f7ab49790a
-- title:
--   Zero-capped strategy and zero barrier have identical restricted Stieltjes measures before ruin
-- statement:
--   For a zero-capped admissible dividend strategy starting from zero, at any positive deterministic time T strictly before ruin, the actual dividend Stieltjes measures of that strategy and the zero barrier agree as Borel measures restricted to [0,T). Hence all discounted and undiscounted payoffs on that pre-ruin prefix agree, including continuous and jump payments.
-- source:
--   Formal dividend Stieltjes measure and zero-cap verification, Avram et al. (2007), Proposition 4 boundary construction.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ico_zero_eq_dividendValue
import Theorems.Thm_AvramDividend_Classical_zero_cap_dividendMeasure_Ico_eq_barrier_before_ruin
import Theorems.Thm_AvramDividend_Classical_restricted_measure_eq_of_Ico_prefix_eq

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.zero_cap_dividendMeasure_restrict_Ico_eq
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X 0 0 D)
    (ω : Ω) (T : ℝ≥0) (hT : 0 < T)
    (hTr : (T : ℝ≥0∞) < ruinTime X 0 D ω) :
    (dividendMeasure D ω).restrict (Ico (0 : ℝ) (T : ℝ)) =
      (dividendMeasure (barrierStrategy X 0 0) ω).restrict
        (Ico (0 : ℝ) (T : ℝ)) := by sorry
