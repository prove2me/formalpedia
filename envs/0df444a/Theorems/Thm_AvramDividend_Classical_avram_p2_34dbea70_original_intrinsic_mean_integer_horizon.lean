-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_original_intrinsic_mean_integer_horizon
-- name    : AvramDividend.Classical.avram_p2_34dbea70_original_intrinsic_mean_integer_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T15:31:44.976907+00:00
-- url     : https://prove2.me/theorems/500b6623-897b-455a-b30b-be3ef270808d
-- title:
--   Original intrinsic marked jump-count mean scales exactly on integer horizons
-- statement:
--   For the unchanged source process and any Borel mark set, the ENNReal expected intrinsic marked count on (0,n] is n times that on (0,1]. Follows solely from proved original stationary horizon additivity and the empty-horizon identity, without presupposing Levy intensity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_original_marked_mean_additive_horizon_no_hypothesis

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p2_34dbea70_original_intrinsic_mean_integer_horizon {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (B : Set ℝ)
    (hB : MeasurableSet B) (n : ℕ) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 =>
        (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 (n : ℝ≥0) ×ˢ B) ∂P) =
    n • (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 =>
        (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 (1 : ℝ≥0) ×ˢ B) ∂P) := by sorry
