-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_run1640_original_intrinsic_marked_general_interval_partition
-- name    : AvramDividend.Classical.avram_p4_s3_run1640_original_intrinsic_marked_general_interval_partition
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:23:03.159356+00:00
-- url     : https://prove2.me/theorems/41e82238-cf8b-4e8c-a09c-7fa74bf8427e
-- title:
--   Original Lévy marked-jump measure partitions exactly on every triple of deterministic clock times
-- statement:
--   For any original spectrally negative Lévy sample path and Borel mark B, and any a≤s≤t, marked jumps on (a,t] split exactly into those on (a,s] and (s,t]. The pathwise identity is in ENNReal and applies without any finite-count or distributional assumption, including grids that do not start at zero.
-- source:
--   Prove literal disjoint half-open measurable-product set partition under a≤s≤t, then exact count-restricted/map measure_union, no stochastic assumption or stationary law.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_run1640_original_intrinsic_marked_general_interval_partition
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (a s t : ℝ≥0) (has : a ≤ s) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B) :
    let J : Set ℝ≥0 → ℝ≥0∞ := fun I =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (I ×ˢ B)
    J (Ioc a t) = J (Ioc a s) + J (Ioc s t) := by sorry
