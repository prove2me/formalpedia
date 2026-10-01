-- Prove2me | Theorems.Thm_AvramDividend_Classical_dividendValue_le_of_hjb
-- name    : AvramDividend.Classical.dividendValue_le_of_hjb
-- status  : Open
-- author  : @WillR
-- created : 2026-09-30T20:56:16.936304+00:00
-- url     : https://prove2.me/theorems/d793cc52-9cad-4acf-9019-f1becd717c86
-- title:
--   Fixed-strategy local HJB verification bound
-- statement:
--   For a fixed dividend strategy D admissible under cap C, if w has the continuity and smoothness required by the verification theorem and satisfies the HJB equation below C, then the expected discounted dividends paid by D from any initial capital x in [0,C] are at most w(x).
-- source:
--   Avram, Palmowski and Pistorius, arXiv:math/0702893v1, Proposition 4(i), pp. 18–19. The proof fixes an arbitrary strategy in Π_{≤C}, applies the appropriate Itô/change-of-variable formula to the discounted candidate along the controlled surplus up to localising stopping times, uses the HJB inequalities, and passes to the limit by monotone convergence. The supremum over strategies is taken only afterwards.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem dividendValue_le_of_hjb {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth :
      (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) :
    dividendValue X q x D ≤ ENNReal.ofReal (w x) := by sorry

end AvramDividend.Classical
