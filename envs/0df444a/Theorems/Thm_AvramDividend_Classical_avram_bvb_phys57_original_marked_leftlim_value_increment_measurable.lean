-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_phys57_original_marked_leftlim_value_increment_measurable
-- name    : AvramDividend.Classical.avram_bvb_phys57_original_marked_leftlim_value_increment_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T16:37:57.032782+00:00
-- url     : https://prove2.me/theorems/36d53653-e6c2-4da3-bbca-c34aa3acf154
-- title:
--   Original predictable reserve marked value-increment measurability
-- statement:
--   For the original dividend strategy, the predictable reserve left limit and the positive-continuity extension of the candidate value function make its marked jump-value increment jointly measurable.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb_phys57_original_marked_leftlim_value_increment_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) :
    let U : ℝ≥0 → Ω → ℝ := fun t ω => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
    Measurable[(@Prod.instMeasurableSpace _ _
      (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))]
      (fun p : (ℝ≥0 × Ω) × ℝ =>
        w (U p.1.1 p.1.2 + p.2) - w (U p.1.1 p.1.2)) := by sorry
