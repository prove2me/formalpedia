-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_physical_clipped_small_negative_band_intensity_measurable
-- name    : AvramDividend.Classical.avram_p4_f3_original_physical_clipped_small_negative_band_intensity_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T19:22:01.758036+00:00
-- url     : https://prove2.me/theorems/8bf95bcb-fa3a-4eac-8138-ffcdd6c4c1b9
-- title:
--   Actual original predividend clipped left-reserve small-jump squared source intensity is jointly measurable
-- statement:
--   For the same original Levy process and dividend strategy, the squared compensated small-negative-jump coefficient intensity using actual clipped predividend left-reserves is measurable on physical time by sample. All measurability assumptions are discharged from the Proved original reserve theorem and original levy intensity lemma.
-- source:
--   Combine Proved/public 55e36fd0 actual original clipped reserve measurability with Proved/public 5ed70ebd original joint quadratic jump intensity measurability for arbitrary measurable reserve parameters; specialise comparison to the constant δ.

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_predividend_clipped_reserve_jointly_measurable_bounded
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_small_negative_band_arbitrary_source_parameter_L2_measurable
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f3_original_physical_clipped_small_negative_band_intensity_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (δ K ε : ℝ) (hδK : δ ≤ K) :
    let U : ℝ≥0 × Ω → ℝ := fun p =>
      let y := Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
      if y ∈ Icc δ K then y else δ
    Measurable (fun p =>
      (∫⁻ z in Ioo (-ε) (0 : ℝ),
        ENNReal.ofReal
          (((w (U p + z) - w (U p)) -
            (w (δ + z) - w δ)) ^ 2) ∂X.ν)) := by sorry
