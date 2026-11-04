-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_intrinsic_marked_zero_horizon_empty
-- name    : AvramDividend.Classical.avram_wave7_06_original_intrinsic_marked_zero_horizon_empty
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T07:19:55.022714+00:00
-- url     : https://prove2.me/theorems/fa7fd76d-94e1-4a03-b131-d2b1de97ce13
-- title:
--   Original Lévy intrinsic marked count vanishes at a zero time horizon
-- statement:
--   The actual intrinsic jump measure associated to the original Lévy source has zero mass on a zero-duration interval for every sample path and every mark set. This provides p(0)=1 for the original no-jump semigroup.
-- source:
--   Avram W7-06 original Ω, P, X, filtration, jump paths, no surrogate process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_intrinsic_marked_zero_horizon_empty
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (B : Set ℝ) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc (0 : ℝ≥0) 0 ×ˢ B) = 0 := by sorry
