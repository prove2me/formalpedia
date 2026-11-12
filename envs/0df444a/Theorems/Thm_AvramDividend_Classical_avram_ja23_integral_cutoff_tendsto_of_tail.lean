-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja23_integral_cutoff_tendsto_of_tail
-- name    : AvramDividend.Classical.avram_ja23_integral_cutoff_tendsto_of_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T16:57:54.894196+00:00
-- url     : https://prove2.me/theorems/6aac909c-f5f3-45f6-b6e4-9216feb0383b
-- title:
--   Finite marked strip quadratic integral converges to full open tail
-- statement:
--   If an integrable quadratic interval is split at cutoffs approaching its endpoint and the remaining quadratic tail integral vanishes, then the strip integral converges to the complete interval integral.
-- source:
--   J-A23 deterministic source variance passage towards e5df71c0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ja23_integral_cutoff_tendsto_of_tail
    (μ : Measure ℝ) (a : ℝ) (b : ℕ → ℝ)
    (hOrder : ∀ᶠ m in atTop, a ≤ b m ∧ b m < 0)
    (hI : IntegrableOn (fun z : ℝ => z ^ 2) (Ioo a 0) μ)
    (hTail : Tendsto
      (fun m : ℕ => ∫ z in Ioo (b m) 0, z ^ 2 ∂μ)
      atTop (nhds (0 : ℝ))) :
    Tendsto
      (fun m : ℕ => ∫ z in Ioc a (b m), z ^ 2 ∂μ)
      atTop (nhds (∫ z in Ioo a 0, z ^ 2 ∂μ)) := by sorry
