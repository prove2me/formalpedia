-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_unrestricted_upper_bound_of_generator
-- name    : AvramDividend.Classical.vcstar_unrestricted_upper_bound_of_generator
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T06:33:03.568007+00:00
-- url     : https://prove2.me/theorems/bec18d51-285f-46d3-b198-a1ce7acc0294
-- title:
--   The candidate vcstar bounds the unrestricted value function under the generator inequality above c*
-- statement:
--   Under the hypotheses of Theorem 2, assume in addition that the generator residual Gamma vcstar - q vcstar is integrable and nonpositive above c*. Then vcstar dominates the unrestricted dividend value function at every x>=0. This is the verification/comparison half of Theorem 2(ii), obtained by combining q-harmonicity below the barrier, derivative at least one, the supplied generator inequality above the barrier, and the global verification theorem.
-- source:
--   Avram, Palmowski and Pistorius (2007), Lemmas 3-4, Proposition 4(i) and Theorem 2(ii), pp.14-21.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem vcstar_unrestricted_upper_bound_of_generator
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨ ContDiffOn ℝ 2 (vcstar W) (Ioi 0))
    (hgen : ∀ y : ℝ, (cstar W).toReal < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        X.generator (vcstar W) y - q * vcstar W y ≤ 0) :
    ∀ x : ℝ, 0 ≤ x →
      valueFunction X q x ≤ ENNReal.ofReal (vcstar W x) := by sorry

end AvramDividend.Classical
