-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja22_original_finite_activity_real_levy_tail_square_tendsto_zero
-- name    : AvramDividend.Classical.avram_ja22_original_finite_activity_real_levy_tail_square_tendsto_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T16:19:35.88205+00:00
-- url     : https://prove2.me/theorems/2eefaa43-2b55-4011-9178-5960ac4c627b
-- title:
--   Finite-activity original Levy nearzero real quadratic energy vanishes
-- statement:
--   The real-valued integrated mark square on the omitted nearzero negative Levy band tends to zero for a finite activity Levy measure; direct by quadratic bound and n inverse-squared limit.
-- source:
--   J-A22 corrected Gaussian original bracket limit, Proved 92557e63.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja22_original_finite_activity_real_levy_tail_square_tendsto_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    Tendsto
      (fun n : ℕ =>
        ∫ z in Ioo (-(1 / ((n : ℝ) + 1))) 0, z ^ 2 ∂X.ν)
      atTop (nhds (0 : ℝ)) := by sorry
