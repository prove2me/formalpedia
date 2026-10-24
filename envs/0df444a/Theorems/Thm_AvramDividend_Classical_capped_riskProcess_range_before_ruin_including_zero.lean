-- Prove2me | Theorems.Thm_AvramDividend_Classical_capped_riskProcess_range_before_ruin_including_zero
-- name    : AvramDividend.Classical.capped_riskProcess_range_before_ruin_including_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T21:56:13.135341+00:00
-- url     : https://prove2.me/theorems/15c076b4-b5f4-4b35-a392-5b8aac1cc0a9
-- title:
--   Capped admissible reserves stay in the verification-function domain at every time strictly before ruin, including time zero
-- statement:
--   For a capped admissible strategy starting with nonnegative capital x within the cap C, the controlled reserve at every time strictly before ruin is nonnegative and has ENNReal.ofReal value at most C. At positive times the cap follows from IsAdmissibleLe and nonnegativity follows from riskProcess_nonneg_before_ruin. At zero, the Lévy and dividend processes both start at zero, so the reserve equals x and the initial-cap hypotheses apply. This is the exact domain condition for applying the candidate w along the stopped controlled reserve.
-- source:
--   Canonically Proved riskProcess_nonneg_before_ruin (c26c83f7-d703-46b9-a361-bf008b70dfe6); Definitions.Def_AvramDividend_Classical_DividendStrategy (IsAdmissibleLe, IsDividendStrategy, riskProcess) and SpectrallyNegativeLevy.X_zero.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_riskProcess_nonneg_before_ruin

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.capped_riskProcess_range_before_ruin_including_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (hx : 0 ≤ x)
    (C : ℝ≥0∞) (hxC : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0)
    (ht : (t : ℝ≥0∞) < ruinTime X x D ω) :
    0 ≤ riskProcess X x D t ω ∧
      ENNReal.ofReal (riskProcess X x D t ω) ≤ C := by sorry
