-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_intrinsic_marked_jump_measure_sigma_finite_each_original_path
-- name    : AvramDividend.Classical.avram_wave5_01_actual_intrinsic_marked_jump_measure_sigma_finite_each_original_path
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T09:54:29.714258+00:00
-- url     : https://prove2.me/theorems/409ca60f-48af-4148-a44b-dd3d91c39af7
-- title:
--   Actual original pathwise Lévy marked jump measure is sigma-finite, including UBV
-- statement:
--   The literal intrinsic marked jump measure of every actual SpectrallyNegativeLevy P 𝓕 sample path is σ-finite on ℝ≥0×ℝ, without BV or a Poisson probability-space replacement. The source graph is countable and Borel; source singleton atoms have mass at most one by the Proved singleton time-atom identity; these yield an explicit countable finite-mass cover.
-- source:
--   Original countable Borel marked path support 7a4d6307 (once Proved), original singleton marked measure exact 74f501cd, Mathlib Measure.sigmaFinite_of_countable.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_marked_jump_measure_countable_borel_support
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_jump_measure_single_time_atom_exact

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_01_actual_intrinsic_marked_jump_measure_sigma_finite_each_original_path
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) :
    SigmaFinite
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) := by sorry
