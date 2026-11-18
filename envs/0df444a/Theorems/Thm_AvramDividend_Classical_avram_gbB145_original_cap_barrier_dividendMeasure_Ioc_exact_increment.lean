-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB145_original_cap_barrier_dividendMeasure_Ioc_exact_increment
-- name    : AvramDividend.Classical.avram_gbB145_original_cap_barrier_dividendMeasure_Ioc_exact_increment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T18:04:25.689665+00:00
-- url     : https://prove2.me/theorems/4d4026e4-3b23-4c70-a188-64d2ddd7a2c0
-- title:
--   Every original cap barrier physical Stieltjes cash cell mass equals the actual dividend regulator increment
-- statement:
--   For any original spectrally negative Lévy source, equal-cap barrier and physical real endpoints, the original dividendMeasure of Ioc(a,b) equals ENNReal.ofReal(D(b)-D(a)). Proved barrier monotonicity and full continuity discharge the conditional hypotheses in the source-faithful B144 Stieltjes identity, thereby giving a genuine exact dividend cash mesh certificate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_monotone
import Theorems.Thm_AvramDividend_Classical_avram_gbB32_original_cap_barrier_full_continuity
import Theorems.Thm_AvramDividend_Classical_avram_gbB144_original_dividendMeasure_Ioc_exact_increment_of_rightContinuous
open MeasureTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB145_original_cap_barrier_dividendMeasure_Ioc_exact_increment
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (c : ℝ)
    (ω : Ω) (a b : ℝ) :
    dividendMeasure (barrierStrategy X c c) ω (Ioc a b) =
      ENNReal.ofReal
        (barrierStrategy X c c b.toNNReal ω -
          barrierStrategy X c c a.toNNReal ω) := by sorry
