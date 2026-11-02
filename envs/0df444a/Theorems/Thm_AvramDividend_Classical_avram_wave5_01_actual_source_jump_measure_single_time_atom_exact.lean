-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_jump_measure_single_time_atom_exact
-- name    : AvramDividend.Classical.avram_wave5_01_actual_source_jump_measure_single_time_atom_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T08:49:40.133652+00:00
-- url     : https://prove2.me/theorems/74f501cd-fa7c-449d-81c1-c6f15b843252
-- title:
--   The genuine original Lévy jump measure has exactly the original path jump indicator as its time atom
-- statement:
--   For every genuine source sample path, any deterministic time t and Borel mark band B, the literal original jump counting measure of {t}×B equals the extended cardinality of source times u=t with 0<u, nonzero original path jump and actual jump mark in B. Thus the atom is exactly one if the source jump meets the condition, and zero otherwise. This is a pathwise identity with no BV, independent copy, or filtration substitution.
-- source:
--   Source joint Borel jump-mark theorem 9d68c5c2 and elementary count.restrict.map on singleton time sections.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_joint_measurable

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_01_actual_source_jump_measure_single_time_atom_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (t : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      ({t} ×ˢ B) =
    ({u : ℝ≥0 | u = t ∧ 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∈ B}).encard := by sorry
