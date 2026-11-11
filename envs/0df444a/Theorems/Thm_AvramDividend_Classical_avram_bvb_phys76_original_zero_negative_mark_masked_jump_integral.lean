-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_phys76_original_zero_negative_mark_masked_jump_integral
-- name    : AvramDividend.Classical.avram_bvb_phys76_original_zero_negative_mark_masked_jump_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T00:56:01.476148+00:00
-- url     : https://prove2.me/theorems/336e335f-e28c-49dc-8813-39b603e41679
-- title:
--   Original intrinsic zero negative marked count annihilates every stopped supported jump cash integral
-- statement:
--   For the true original intrinsic marked measure NX on the same sample path, if the negative mark count in the physical horizon is zero, then the actual signed jump integral of any measurable-time stopped kernel that vanishes outside the same strict-time negative-mark rectangle is zero, independently of auxiliary processes or compensation. This is the jump side of M_n in the original c37acb5a physical-grid ledger.
-- source:
--   Original stopped marked-measure zero set and MeasureTheory.integral_eq_zero_of_ae

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bvb_phys76_original_zero_negative_mark_masked_jump_integral
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0)
    (hZero : ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim
        (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ Iio (0 : ℝ)) = 0)
    (H : ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hSupport : ∀ p : ℝ≥0 × ℝ, H ((p.1, ω), p.2) ≠ 0 →
      p ∈ Ioc (0 : ℝ≥0) T ×ˢ Iio (0 : ℝ)) :
    (∫ p, H ((p.1, ω), p.2)
      ∂((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) u)))) = 0 := by sorry
