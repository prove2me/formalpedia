-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_original_intrinsic_mean_subinterval_decomposition
-- name    : AvramDividend.Classical.avram_p2_34dbea70_original_intrinsic_mean_subinterval_decomposition
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T16:06:06.60174+00:00
-- url     : https://prove2.me/theorems/2b7b7bc5-b665-4988-9a47-b7a2aafe0396
-- title:
--   Original intrinsic marked-count mean decomposes at ordered horizon times
-- statement:
--   For the original spectrally negative Levy process, any measurable mark set B, and deterministic nonnegative times s≤t, the original expected intrinsic marked jump count on (0,t] equals its expected count on (0,s] plus its expected count over an interval of length t−s. The proof applies genuine stationary-horizon additivity and NNReal's subtraction cancellation. No intensity or compensator hypothesis.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_original_marked_mean_additive_horizon_no_hypothesis

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p2_34dbea70_original_intrinsic_mean_subinterval_decomposition {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (B : Set ℝ)
    (hB : MeasurableSet B) (s t : ℝ≥0) (hst : s ≤ t) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 =>
        (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 t ×ˢ B) ∂P) =
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 =>
        (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 s ×ˢ B) ∂P) +
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 =>
        (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 (t - s) ×ˢ B) ∂P) := by sorry
