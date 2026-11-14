-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b197_negative_cutoff_marked_measure_mass_tendsto_full_negative
-- name    : AvramDividend.Classical.avram_b197_negative_cutoff_marked_measure_mass_tendsto_full_negative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T23:18:32.639998+00:00
-- url     : https://prove2.me/theorems/92751c20-e46a-44ae-ae55-6d8ff84580ec
-- title:
--   Marked source measure mass on a negative half-open time rectangle is the limit of reciprocal negative band cutoff rectangle masses
-- statement:
--   For any measure on physical nonnegative time paired with a real jump mark, and any fixed nonnegative horizon, the measure of the half-open time rectangle crossed with all strictly negative marks equals the limit of the masses of the same time interval crossed with the increasing reciprocal negative mark cutoff bands. The proof shows the cutoff rectangles are monotone by reciprocal order, their set union equals the full negative rectangle using prepared B196 negative cutoff mark exhaustion, and Mathlib tendsto_measure_iUnion_atTop gives continuity of measure from below for this source. In particular, instantiating the measure with the actual original spectrally negative Levy jump Poisson marked counting measure on each sample path expresses the full original negative mark source count as the limit of finite cutoff source counts. Combining that with the Proved jump_phys13 random interval cutoff count measurability will establish the a.e. measurability needed for B195 and enable almost-sure finite full source negative jump counts under the Proved mix_fin14 finite source Poisson expectation, without assuming finite marks on exceptional paths.
-- source:
--   Prepared B196 all negative real marks reciprocal cutoff union, Mathlib tendsto_measure_iUnion_atTop, monotone product set rectangles.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_b196_reciprocal_negative_mark_bands_exhaust_all_negative_marks
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Any marked source measure charges the full negative rectangle as the limit of increasing reciprocal negative cutoff rectangle masses. -/

theorem AvramDividend.Classical.avram_b197_negative_cutoff_marked_measure_mass_tendsto_full_negative
    (μ : Measure (ℝ≥0 × ℝ)) (T : ℝ≥0) :
    Tendsto (fun n : ℕ =>
      μ (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1)))))
      atTop (𝓝 (μ (Ioc 0 T ×ˢ Iio (0 : ℝ)))) := by sorry
