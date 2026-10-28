-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_scale_C1_zero_discount_core
-- name    : AvramDividend.Classical.unbounded_scale_C1_zero_discount_core
-- status  : Open
-- author  : @WillR
-- created : 2026-10-25T07:19:34.23933+00:00
-- url     : https://prove2.me/theorems/8aaa16d2-d9ec-4e8f-8e42-cc551cca9d8d
-- title:
--   C1 regularity of an unbounded-variation zero-discount scale function
-- statement:
--   Precisely isolates the q=0 regularity case of the root-connected Open target scaleFunction_contDiff_one_of_unbounded_variation_nonpositive_q (8b23cd38-7b0a-4469-bfb1-90feef46733d). The complementary q<0 branch is impossible, established by canonical Proved unbounded_scaleFunction_negative_q_impossible (d14a3b03-1013-4a7e-8171-0d20a4fa2dc0). Proving this zero-discount core therefore closes the exact original q≤0 regularity theorem through a short case split, with no dependency on the original parent.
-- source:
--   Original Prove2Me theorem scaleFunction_contDiff_one_of_unbounded_variation_nonpositive_q; Proved negative-q impossibility helper d14a3b03-1013-4a7e-8171-0d20a4fa2dc0.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_scale_C1_zero_discount_core
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (W : ℝ → ℝ) (hW : IsScaleFunction X 0 W)
    (hnbv : ¬ X.BoundedVariation) :
    ContDiffOn ℝ 1 W (Ioi (0 : ℝ)) := by sorry
