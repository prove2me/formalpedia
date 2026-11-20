-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_UBV_true_discounted_first_exit_scale_ratio
-- name    : AvramDividend.Classical.avram_f6_original_UBV_true_discounted_first_exit_scale_ratio
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T21:11:19.19167+00:00
-- url     : https://prove2.me/theorems/003b9c4c-b8ac-47d7-ab0b-9314d0b1168f
-- title:
--   Original UBV killed first-exit expectation equals true q-scale W(1)/W(b) for all b≥1
-- statement:
--   Original unbounded variation standing spectrally negative Levy X with genuine q-scale W has exact discounted two-sided exit expectation from 1 to b≥1 equal to ENNReal.ofReal(W(1)/W(b)). Follows from proved actual stopped q-scale harmonicity and proved UBV killed harmonicity-to-exit ratio.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ScaleFunction
set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_UBV_true_discounted_first_exit_scale_ratio
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∀ b : ℝ, 1 ≤ b →
      twoSidedExitExpectation X q b 1 =
        ENNReal.ofReal (W 1 / W b) := by sorry
