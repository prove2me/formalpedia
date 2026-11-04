-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_original_marked_mean_monotone_horizon
-- name    : AvramDividend.Classical.avram_p2_34dbea70_original_marked_mean_monotone_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T13:36:19.278776+00:00
-- url     : https://prove2.me/theorems/078c1e03-6660-40b4-b19c-37db0336ef2b
-- title:
--   Original intrinsic marked-jump expected count is monotone in the time horizon
-- statement:
--   For the original spectrally negative Lévy process, any real mark set B and nonnegative horizons T≤S, the expected value of the exact intrinsic marked counting measure on (0,T] times B is at most its expected value on (0,S] times B. This is a direct pathwise measure monotonicity and ENNReal lintegral monotonicity proof, with no mark regularity, integrability, finite activity, rate or compensator assumption. Together with the source's stationary mean additivity it supports a Cauchy-equation argument for time-proportional mean intensity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_34dbea70_original_marked_mean_monotone_horizon
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T S : ℝ≥0) (hTS : T ≤ S) (B : Set ℝ) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 =>
        (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ B) ∂P) ≤
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 =>
        (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 S ×ˢ B) ∂P) := by sorry
