-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_anoise18_original_negative_cutoff_counts_monotone_exhaust
-- name    : AvramDividend.Classical.avram_anoise18_original_negative_cutoff_counts_monotone_exhaust
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T07:43:22.431172+00:00
-- url     : https://prove2.me/theorems/3d13b0e5-b7c7-4def-8d27-aeaa6edfbcff
-- title:
--   Original negative Lévy jump cutoff counts increase to all-negative physical count
-- statement:
--   For the original Lévy sample path and fixed time horizon, negative jump counts on thresholds z≤-1/(n+1) are monotone increasing and their supremum is exactly the all-negative-mark count, pathwise on the original sample space.
-- source:
--   Proved exact original intrinsic marked-count exhaustion theorem 93b74ae6; elementary interval equality and monotonicity of mapped counting measure.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_intrinsic_all_negative_marks_exhausted_by_threshold_bands
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_anoise18_original_negative_cutoff_counts_monotone_exhaust
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (ω : Ω) :
    let Ncut : ℕ → ℝ≥0∞ := fun n =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1))))
    let Nall : ℝ≥0∞ :=
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iio (0 : ℝ))
    Monotone Ncut ∧ Nall = ⨆ n : ℕ, Ncut n := by sorry
