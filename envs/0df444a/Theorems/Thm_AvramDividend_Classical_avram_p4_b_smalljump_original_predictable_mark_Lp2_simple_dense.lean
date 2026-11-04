-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_predictable_mark_Lp2_simple_dense
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_predictable_mark_Lp2_simple_dense
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:14:26.473321+00:00
-- url     : https://prove2.me/theorems/57f21b85-5963-46b5-96d7-74585082b57f
-- title:
--   Actual original predictable small-negative mark Lp2 simple integrands are dense
-- statement:
--   For the original spectrally negative Lévy process X, actual right-continuous predictable time-space measure μ and actual restricted source Lévy measure on (-1,0), the square-integrable finite-valued simple functions form a dense subset of the joint Lp2. This provides a genuine density premise for extending source compensated simple integrals by L2 continuity. It does not establish their isometry, martingale property or identification with original jump counts.
-- source:
--   Pinned Mathlib MeasureTheory.Lp.simpleFunc.denseRange in original source predictable product Lp2, with p=2 finite.

import Mathlib
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_predictable_mark_Lp2_simple_dense
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable)) :
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
      DenseRange
        (Subtype.val :
          ↥(Lp.simpleFunc ℝ (2 : ℝ≥0∞)
            (μ.prod (X.ν.restrict (Ioo (-1 : ℝ) 0)))) →
          Lp ℝ (2 : ℝ≥0∞)
            (μ.prod (X.ν.restrict (Ioo (-1 : ℝ) 0))))) := by sorry
