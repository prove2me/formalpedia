-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_original_zero_horizon_intrinsic_jump_rate
-- name    : AvramDividend.Classical.avram_p2_original_zero_horizon_intrinsic_jump_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:42:10.178277+00:00
-- url     : https://prove2.me/theorems/d5ca282e-5ee1-4911-a0c9-091295bfce9d
-- title:
--   Zero-horizon intrinsic original Lévy jump rate for every mark set
-- statement:
--   At T=0 the intrinsic zero-origin count for the actual càdlàg original process has empty time support, hence its expected count is exactly 0 times the actual Lévy measure, for any Borel or non-Borel mark set B. This removes the degenerate-horizon branch from the final arbitrary-horizon separated-band jump-intensity theorem, without any compensator or path assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_original_zero_horizon_intrinsic_jump_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (B : Set ℝ) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 (0 : ℝ≥0) ×ˢ B) ∂P) =
      (0 : ℝ≥0∞) * X.ν B := by sorry
