-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_marked_measure_arbitrary_set_negative_support
-- name    : AvramDividend.Classical.avram_wave7_01_original_intrinsic_marked_measure_arbitrary_set_negative_support
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T14:40:31.552484+00:00
-- url     : https://prove2.me/theorems/b4f7e14b-fa0b-4895-add5-431a8c78a5e5
-- title:
--   Global original intrinsic Lévy jump measure is supported on negative marks for every time–mark test set
-- statement:
--   On the exact source Ω, P, X, the actual intrinsic jump counting measure has no nonnegative marks. Consequently its measure of every time-mark subset S, even not assumed Borel, is unchanged upon intersection with the strictly negative-mark half-plane. This strengthens rectangle support to arbitrary stopping domains and pathwise time-mark tests, with no BV or finite-activity assumption.
-- source:
--   Preexisting proved exact original intrinsic global nonnegative mark support zero (0a9afdb9-4d96-45fb-998e-d7a78f798a44); measure monotonicity, subadditivity, and the ℝ dichotomy.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_intrinsic_marked_measure_global_nonnegative_support_zero

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_01_original_intrinsic_marked_measure_arbitrary_set_negative_support
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (S : Set (ℝ≥0 × ℝ)) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      S =
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (S ∩ (Set.univ ×ˢ Iio (0 : ℝ))) := by sorry
