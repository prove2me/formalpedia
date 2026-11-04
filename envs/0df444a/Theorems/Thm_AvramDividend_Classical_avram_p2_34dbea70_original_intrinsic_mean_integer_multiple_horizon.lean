-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_original_intrinsic_mean_integer_multiple_horizon
-- name    : AvramDividend.Classical.avram_p2_34dbea70_original_intrinsic_mean_integer_multiple_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T15:49:59.90297+00:00
-- url     : https://prove2.me/theorems/0e509107-df29-4190-9ae7-12fdf60867fb
-- title:
--   Original intrinsic marked jump-count means scale on every integer time multiple
-- statement:
--   For the original spectrally negative Levy process and any measurable mark set B, the expected intrinsic marked jump count on (0,n*t] equals n times its expected count on (0,t]. This is proved by induction using established original-process stationary-horizon additivity. It holds for arbitrary nonnegative horizon t and makes no Poisson or intensity assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_original_marked_mean_additive_horizon_no_hypothesis

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p2_34dbea70_original_intrinsic_mean_integer_multiple_horizon {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (B : Set ℝ)
    (hB : MeasurableSet B) (t : ℝ≥0) (n : ℕ) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 =>
        (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 (n • t) ×ˢ B) ∂P) =
    n • (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 =>
        (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 t ×ˢ B) ∂P) := by sorry
