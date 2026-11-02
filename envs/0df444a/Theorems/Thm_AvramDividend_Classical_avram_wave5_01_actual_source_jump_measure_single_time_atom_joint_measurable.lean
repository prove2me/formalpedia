-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_jump_measure_single_time_atom_joint_measurable
-- name    : AvramDividend.Classical.avram_wave5_01_actual_source_jump_measure_single_time_atom_joint_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T08:55:09.154491+00:00
-- url     : https://prove2.me/theorems/09a68f58-3bd3-48d2-99ed-2a7680e31864
-- title:
--   Original Lévy singleton-time jump measure atom is jointly measurable in actual time and sample
-- statement:
--   For every unchanged spectrally negative Levy source and Borel mark set, the mass of the intrinsic pathwise jump measure on the singleton time slice {t}×B is a jointly measurable function of actual time t and sample ω. It equals the indicator of the original jump at that time. There is no BV, Poisson-copy or filtration substitution. This is the direct source single-time kernel interface needed for genuine time-section integration.
-- source:
--   Accepted source jumpmark joint measurability theorem 9d68c5c2 and newly submitted exact original source single-time atom identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_jump_measure_single_time_atom_exact

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_01_actual_source_jump_measure_single_time_atom_joint_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (B : Set ℝ) (hB : MeasurableSet B) :
    Measurable (fun z : ℝ≥0 × Ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u z.2 - Function.leftLim
          (fun v : ℝ≥0 => X.X v z.2) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u z.2 - Function.leftLim
            (fun v : ℝ≥0 => X.X v z.2) u)))
        ({z.1} ×ˢ B)) := by sorry
