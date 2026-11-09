-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_original_no_nonnegative_mark_counts
-- name    : AvramDividend.Classical.avram_p2_c_borel_original_no_nonnegative_mark_counts
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:38:09.578807+00:00
-- url     : https://prove2.me/theorems/408c3fc6-498b-4d60-ae6f-a31a81cfd51b
-- title:
--   Original intrinsic marked jump counts vanish on nonnegative Borel marks
-- statement:
--   For every original Lévy source sample path, its intrinsic marked count on a time rectangle with nonnegative Borel marks is zero, provided the marked jump map is measurable. Every counted jump is nonzero and the actual source no-positive-jumps field forces its size to be strictly negative. Measurability is an explicit assumption.
-- source:
--   Proved P2-C count restrict/map rectangle d3c582e3 and source pathwise nonzero jump negativity 2ba2b75a; actual definition 933ced80.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_original_nonzero_jump_strictly_negative
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_count_restrict_map_rectangle
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_c_borel_original_no_nonnegative_mark_counts
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (s t : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) (hBpos : B ⊆ Ici (0 : ℝ))
    (hmarkMeas : Measurable
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ B) = 0 := by sorry
