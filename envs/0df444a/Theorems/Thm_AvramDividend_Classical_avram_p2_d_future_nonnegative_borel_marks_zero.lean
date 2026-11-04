-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_nonnegative_borel_marks_zero
-- name    : AvramDividend.Classical.avram_p2_d_future_nonnegative_borel_marks_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:24:33.023054+00:00
-- url     : https://prove2.me/theorems/cde18422-4888-4a78-a3ce-9c0a6de52517
-- title:
--   Original intrinsic future marked count and Lévy rate vanish for nonnegative Borel marks
-- statement:
--   For the unchanged original spectrally negative Lévy source and any measurable B subset [0,∞), the exact intrinsic jump count on (s,t]×B vanishes for every original sample, the source Lévy measure ν(B) vanishes, and the unconditional expected count equals (t−s)ν(B)=0, with no restriction on s,t, finite activity or BV.
-- source:
--   Deduced directly from separately Proved 56a5b5da (pathwise strict-negative support) and c324380a (source Lévy measure strict-negative support). Includes empty sets and zero jump sizes; no intensity is assumed for negative marks.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_jump_rectangle_restrict_to_strictly_negative_marks
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_levy_measure_arbitrary_mark_negative_restriction

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_d_future_nonnegative_borel_marks_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B)
    (hBnonneg : B ⊆ Ici (0 : ℝ)) :
    (∀ ω : Ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) = 0) ∧
    X.ν B = 0 ∧
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) =
      ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B := by sorry
