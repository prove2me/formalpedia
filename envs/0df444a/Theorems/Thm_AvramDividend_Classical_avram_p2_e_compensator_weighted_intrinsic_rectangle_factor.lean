-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_weighted_intrinsic_rectangle_factor
-- name    : AvramDividend.Classical.avram_p2_e_compensator_weighted_intrinsic_rectangle_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:35:53.298192+00:00
-- url     : https://prove2.me/theorems/75e37892-da13-48e5-a2ad-9b320ab9045c
-- title:
--   Actual intrinsic marked Lévy rectangle count factors against every past nonnegative weight
-- statement:
--   For the actual original spectrally negative Lévy process X and its unchanged filtration, any nonnegative F_s-measurable weight W factors in first moment from its literal pathwise marked jump count on (s,t]×B. Precisely E[W N_X((s,t]×B)] = E[W] E[N_X((s,t]×B)] in ENNReal, allowing infinite values. This is the weighted original-source independent-increment step; identifying E[N_X] with (t-s)ν(B) is a separate P2-D obligation.
-- source:
--   Original intrinsic measurable extractor 5cf3e058; independent generic weighted-extractor factor from P2-E fbbf6c10-ae98-4163-acda-d53fa2c0729b (Open until accepted proof). Parent exact source rectangle compensator 393b03a8-2e9a-43d8-b415-854d86d58104.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_e_compensator_weighted_intrinsic_rectangle_factor
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B)
    (W : Ω → ℝ≥0∞) (hW : Measurable[𝓕 s] W) :
    (∫⁻ ω, W ω * ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) =
    (∫⁻ ω, W ω ∂P) *
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) := by sorry
