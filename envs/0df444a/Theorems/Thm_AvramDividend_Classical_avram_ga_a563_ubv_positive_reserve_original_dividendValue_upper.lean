-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a563_ubv_positive_reserve_original_dividendValue_upper
-- name    : AvramDividend.Classical.avram_ga_a563_ubv_positive_reserve_original_dividendValue_upper
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T09:44:28.739858+00:00
-- url     : https://prove2.me/theorems/97caaf76-c13c-480a-b9aa-30cb138741eb
-- title:
--   Unbounded-variation positive-reserve original strategy upper bound
-- statement:
--   For strictly positive initial reserve x, bounded by the original cap C, any original admissible dividend strategy is bounded in discounted value by the smooth HJB supersolution w(x) under non-bounded-variation Lévy dynamics. Retain the full original HJB and admissibility assumptions.
-- source:
--   Avram Palmowski Pistorius Proposition 4(i) stopped Lévy-Ito verification; this helper isolates x>0 and leaves x=0 to the proved zero-start theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a563_ubv_positive_reserve_original_dividendValue_upper
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hxpos : 0 < x) :
    dividendValue X q x D ≤ ENNReal.ofReal (w x) := by sorry
