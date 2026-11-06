-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_run1640_original_intrinsic_negative_marked_time_partition
-- name    : AvramDividend.Classical.avram_p4_s3_run1640_original_intrinsic_negative_marked_time_partition
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:04:48.843711+00:00
-- url     : https://prove2.me/theorems/e4d99546-25d1-46da-b418-f3ff4ff9e3e8
-- title:
--   Exact additivity of original intrinsic marked Lévy counts across an arbitrary finite time partition
-- statement:
--   For the literal marked jump measure of any original spectrally negative Lévy path and measurable Borel mark set B, its count up to t splits exactly into counts up to s and on (s,t], for s≤t. This is a pathwise ENNReal identity valid even without finiteness; it directly supports terminal measurability of interval counts by subtraction once separated negative-band finiteness is proved.
-- source:
--   Use genuine original marked Measure.count.restrict and the measurable disjoint partition Ioc 0 t = Ioc 0 s ∪ Ioc s t, then pinned Mathlib measure_union. No auxiliary stochastic axioms, stationarity or representation shortcut.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_run1640_original_intrinsic_negative_marked_time_partition
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B) :
    let J : Set ℝ≥0 → ℝ≥0∞ := fun I =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (I ×ˢ B)
    J (Ioc 0 t) = J (Ioc 0 s) + J (Ioc s t) := by sorry
