-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f16_original_levy_countable_upper_exit_isStoppingTime
-- name    : AvramDividend.Classical.avram_f16_original_levy_countable_upper_exit_isStoppingTime
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T08:19:10.541809+00:00
-- url     : https://prove2.me/theorems/f40f05e7-9630-462f-8a4b-11360eedbcf8
-- title:
--   Original Lévy countable upper-exit time is a right-continuous-filtration stopping time
-- statement:
--   For every original adapted spectral-negative Levy process, the infimum of deterministic countable observation clocks gated by actual X_t exceeding an upper barrier is a stopping time of the original right-continuous filtration.
-- source:
--   Direct one-sided adaptation of the already Proved exact original countable postpayment-reserve exit clock 4e7e60dd, using X.adapted and 𝓕.le_rightCont.

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_f16_original_levy_countable_upper_exit_isStoppingTime
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (r : ℕ → ℝ≥0) (upper : ℝ) :
    IsStoppingTime 𝓕.rightCont
      (fun ω : Ω => ⨅ j : ℕ,
        if upper < X.X (r j) ω
        then (r j : WithTop ℝ≥0) else ⊤) := by sorry
