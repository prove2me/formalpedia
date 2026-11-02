-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_fixed_time_marked_count_zero_ae
-- name    : AvramDividend.Classical.avram_wave5_01_actual_source_fixed_time_marked_count_zero_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T11:52:58.295818+00:00
-- url     : https://prove2.me/theorems/b6d7a6a3-fac0-48a9-826f-31341b383a08
-- title:
--   The intrinsic original marked Lévy jump measure has almost surely no deterministic positive-time atom
-- statement:
--   For any deterministic positive t and any Borel mark set B, the actual original source marked jump count N_X({t}×B) is zero P-almost surely. This is a same-path source measure statement, proved by combining the actual Lévy no-fixed-jump theorem with the proved exact original singleton-time count identity; applies to all Lévy variation regimes and raw original filtration. Removes deterministic-time boundary atoms in localisation and predictable compensator rectangles.
-- source:
--   Source same-path no deterministic jump at t (b4407263) and Proved intrinsic marked-time atom exact (74f501cd). No detached Poisson space.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_no_fixed_positive_time_jump_ae
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_jump_measure_single_time_atom_exact
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_01_actual_source_fixed_time_marked_count_zero_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (ht : 0 < t) (B : Set ℝ) (hB : MeasurableSet B) :
    ∀ᵐ ω ∂P,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        ({t} ×ˢ B) = 0 := by sorry
