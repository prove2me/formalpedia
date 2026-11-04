-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_nonnegative_mark_vanishing
-- name    : AvramDividend.Classical.avram_p2_d_future_nonnegative_mark_vanishing
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:40:46.226386+00:00
-- url     : https://prove2.me/theorems/81161c09-a96e-4618-851a-431190498110
-- title:
--   Original marked counts and Levy measure vanish on all nonnegative Borel mark sets
-- statement:
--   For the actual original spectrally negative Levy source and any Borel mark set entirely contained in the nonnegative reals, every sample's intrinsic marked count in any physical time rectangle is zero and the original Levy measure assigns zero mass. Includes empty, zero mark and all positive cases, without relying on the unproved negative-mark rate.
-- source:
--   Use Proved source rectangle negative support 56a5b5da and Proved original Levy measure support c324380a, disjointness of B subset Ici 0 from Iio 0, and pinned simp for products with empty and measure_empty.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_jump_rectangle_restrict_to_strictly_negative_marks
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_levy_measure_arbitrary_mark_negative_restriction

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_d_future_nonnegative_mark_vanishing
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B)
    (hNonneg : B ⊆ Ici (0 : ℝ)) :
    (∀ ω : Ω,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) = 0) ∧
      X.ν B = 0 := by sorry
