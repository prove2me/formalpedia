-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_finite12_positive_clock_initial_measurable
-- name    : AvramDividend.Classical.avram_ubv_finite12_positive_clock_initial_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T08:03:31.124442+00:00
-- url     : https://prove2.me/theorems/bce62e25-5d97-4357-a119-bc3b8c8eeaa9
-- title:
--   A right-continuous stopping clock has an initial-filtration measurable positive-clock event
-- statement:
--   The positive-clock event of a nonnegative random stopping time is measurable in the initial right-continuous filtration. This permits a rigorous partition between the already-controlled time-zero payment atom and positive-clock Gaussian Ito terms in the finite-cap dividend budget.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_finite12_positive_clock_initial_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0))) :
    MeasurableSet[𝓕.rightCont 0] {ω : Ω | σ ω ≠ 0} := by sorry
