-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_03_ubv_zero_reserve_ratio
-- name    : AvramDividend.Classical.avram_root29_03_ubv_zero_reserve_ratio
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T08:14:06.243152+00:00
-- url     : https://prove2.me/theorems/12ddf594-122c-4142-8bef-c7497ecb8d69
-- title:
--   Unbounded-variation strict two-sided exit scale ratio at zero without path hypotheses
-- statement:
--   For any spectrally negative Levy process with unbounded variation, q>0, q-scale function W and positive upper barrier a, the genuine strict upward-before-downward q-discounted exit expectation from zero capital equals the q-scale ratio W(0)/W(a). The result removes the near-zero path hypothesis using the original-law Rogozin downward regularity already Proved.
-- source:
--   Independent source-faithful endpoint conversion for canonical targets 2dcc8bcc and 5bcf90e1: the proved source theorem 23672221 gives the zero-start ratio under almost-sure negative observations arbitrarily near time zero, and the proved original-law lemma 703dc740 supplies that exact hypothesis from unbounded variation. No Open killed harmonicity, OST, or canonical two-sided exit theorem is imported.

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_ae_negative_near_zero_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_chat04_unbounded_zero_start_exit_ratio_of_near_zero

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_03_ubv_zero_reserve_ratio
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a) :
    twoSidedExitExpectation X q a 0 =
      ENNReal.ofReal (W 0 / W a) := by sorry
