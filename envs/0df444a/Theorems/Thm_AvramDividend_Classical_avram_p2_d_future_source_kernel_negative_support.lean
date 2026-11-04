-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_source_kernel_negative_support
-- name    : AvramDividend.Classical.avram_p2_d_future_source_kernel_negative_support
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:24:55.463947+00:00
-- url     : https://prove2.me/theorems/7a4f1250-5dad-4a4a-b9dc-bf5cb7136dd3
-- title:
--   Original s-finite intrinsic marked kernel is supported on strictly negative marks
-- statement:
--   Construct the exact genuine original s-finite marked jump kernel and show that each fibre gives zero measure to every jointly Borel time–mark region whose marks are nonnegative. This is a whole-time arbitrary Borel support statement independent of any Lévy-rate formula.
-- source:
--   Combine the Proved source s-finite jump kernel eb357d08 with the original all-Borel negative support helper c598292d when that helper is canonically Proved. Nonnegative-mark C has empty intersection with univ×Iio 0; every fibre κω equals the intrinsic source count measure.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_actual_source_intrinsic_sfinite_kernel
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_full_time_mark_negative_support

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_d_future_source_kernel_negative_support
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    ∃ κ : Kernel Ω (ℝ≥0 × ℝ), IsSFiniteKernel κ ∧
      (∀ ω, κ ω =
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) ∧
      (∀ (ω : Ω) (C : Set (ℝ≥0 × ℝ)), MeasurableSet C →
        C ⊆ (Set.univ ×ˢ Ici (0 : ℝ)) → κ ω C = 0) := by sorry
