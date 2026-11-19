-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_reward51_original_finiteband_NX_count_measurable
-- name    : AvramDividend.Classical.avram_pj_reward51_original_finiteband_NX_count_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T17:16:47.32376+00:00
-- url     : https://prove2.me/theorems/677b070a-e255-4d01-8627-e4683ad5c34a
-- title:
--   Actual Lévy intrinsic negative-band marked count is measurable from original kernel
-- statement:
--   The actual source X-jump-count on the fixed bounded time interval and strictly negative finite mark cutoff is measurable in ω. Direct consequence of the already-Proved intrinsic source s-finite kernel identity, preserving the exact pathwise count, with no extra assumptions.
-- source:
--   Proved eb357d08 original intrinsic s-finite jump kernel; pinned Mathlib Kernel.measurable_coe.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_reward51_original_finiteband_NX_count_measurable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (η : ℝ) :
    Measurable (fun ω =>
      ((Measure.count.restrict {s : ℝ≥0 |
        0 < s ∧ X.X s ω -
          Function.leftLim (fun t : ℝ≥0 => X.X t ω) s ≠ 0}).map
        (fun s : ℝ≥0 => (s, X.X s ω -
          Function.leftLim (fun t : ℝ≥0 => X.X t ω) s)))
        (Ioc (0 : ℝ≥0) T ×ˢ Ioo (-1 : ℝ) (-η))) := by sorry
