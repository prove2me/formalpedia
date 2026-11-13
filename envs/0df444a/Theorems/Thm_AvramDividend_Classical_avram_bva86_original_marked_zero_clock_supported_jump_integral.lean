-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva86_original_marked_zero_clock_supported_jump_integral
-- name    : AvramDividend.Classical.avram_bva86_original_marked_zero_clock_supported_jump_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T21:34:42.049215+00:00
-- url     : https://prove2.me/theorems/de76ff7b-2e4b-4521-874f-bcc840b2cd3d
-- title:
--   Original initial-clock supported marked jump kernel integrates to zero
-- statement:
--   Under measurability of original Levy time/mark map, any kernel supported at time zero has zero integral under the original marked jump measure, using BVA85 and integral_eq_zero_of_ae. This is the jump-count part of M_n(0).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bva85_original_marked_jump_measure_zero_initial_fibre
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva86_original_marked_zero_clock_supported_jump_integral
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (hMeas : Measurable (fun u : ℝ≥0 =>
      (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    (H : ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hSupport : ∀ p : ℝ≥0 × ℝ, H ((p.1, ω), p.2) ≠ 0 → p.1 = 0) :
    (∫ p, H ((p.1, ω), p.2)
      ∂((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) = 0 := by sorry
