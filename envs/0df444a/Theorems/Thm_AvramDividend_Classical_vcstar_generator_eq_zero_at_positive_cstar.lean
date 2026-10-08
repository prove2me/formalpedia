-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_generator_eq_zero_at_positive_cstar
-- name    : AvramDividend.Classical.vcstar_generator_eq_zero_at_positive_cstar
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T22:43:02.842919+00:00
-- url     : https://prove2.me/theorems/91803827-9c02-4911-969e-c81c0bfc4afc
-- title:
--   Generator equality extends to the strictly positive optimal barrier
-- statement:
--   Show the integrable generator residual Γvcstar-q vcstar vanishes exactly at a strictly positive finite c*, extending its q-harmonicity from the open interval below the barrier. This isolates the continuity/limiting-generator argument which cannot be inferred by substituting the boundary into either strict-side hypothesis. The supplied above-barrier generator inequality is retained among the hypotheses of Theorem 2(ii).
-- source:
--   Avram, Palmowski and Pistorius (2007), generator identity Lemma 4 and verification proof Theorem 2(ii), pp. 17-21. Boundary extension under standing regularity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

namespace AvramDividend.Classical
theorem vcstar_generator_eq_zero_at_positive_cstar
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨ ContDiffOn ℝ 2 (vcstar W) (Ioi 0))
    (hgen : ∀ y : ℝ, (cstar W).toReal < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        X.generator (vcstar W) y - q * vcstar W y ≤ 0) :
    X.GeneratorIntegrable (vcstar W) (cstar W).toReal ∧
      X.generator (vcstar W) (cstar W).toReal -
        q * vcstar W (cstar W).toReal = 0 := by
  sorry
end AvramDividend.Classical
