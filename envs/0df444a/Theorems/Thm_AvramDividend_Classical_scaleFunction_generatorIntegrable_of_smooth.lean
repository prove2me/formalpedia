-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorIntegrable_of_smooth
-- name    : AvramDividend.Classical.scaleFunction_generatorIntegrable_of_smooth
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T20:58:49.173087+00:00
-- url     : https://prove2.me/theorems/f66bbd53-5413-409d-b5ef-3797a4626c14
-- title:
--   The scale function lies in the generator domain under the Lemma 4 smoothness alternatives
-- statement:
--   Analytic domain half of the scale-function generator theorem. Under the standing assumptions, q>0 and the three smoothness alternatives used in Lemma 4, the compensated negative-jump generator integrand of the q-scale function is integrable at every x in (0,a). In the positive-Gaussian branch use C2 regularity of the scale function and the generic C2 jump-integrability theorem. In the bounded-variation branch Condition 3.3 forces absolute continuity of the Lévy measure, which gives C1 regularity, and the first-moment bounded-variation integrability theorem applies. In the explicit C2 branch apply the generic C2 theorem directly.
-- source:
--   Avram, Palmowski and Pistorius (2007), regularity assumptions used in the proof of Lemma 4.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_generatorIntegrable_of_smooth
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 W (Ioo 0 a)) :
    ∀ x ∈ Ioo 0 a, X.GeneratorIntegrable W x := by sorry

end AvramDividend.Classical
