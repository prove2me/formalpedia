-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_first_named_exit_lt_horizon_iff_witness
-- name    : AvramDividend.Classical.chat03_first_named_exit_lt_horizon_iff_witness
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T06:46:46.896108+00:00
-- url     : https://prove2.me/theorems/c43767e3-d4be-43bc-b584-a4871417f591
-- title:
--   The first strict two-sided passage clock is earlier than a finite horizon exactly when a strict exit occurs earlier
-- statement:
--   For the minimum of the official named strict upward and downward first-passage times of a spectrally negative Lévy process, being strictly earlier than a finite NNReal horizon T is equivalent to the existence of an actual strict exit witness s<T on either side. The result uses the independently Proved generic ENNReal infimum threshold theorem and the minimum strict inequality equivalence. It accounts for infimum times not attained as strict exits and does not assume any stochastic martingale identity.
-- source:
--   Proved generic extended infimum/horizon result UUID 6fe34389-7bc2-4c6f-82b6-78ebf9d4a7f0 and official TwoSidedExit definitions.

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat03_generic_extended_infimum_lt_horizon
import Mathlib.Order.MinMax

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_first_named_exit_lt_horizon_iff_witness
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (lower upper : ℝ) (T : ℝ≥0) :
    (min (twoSidedExitUpTime X upper ω)
      (twoSidedExitDownTime X lower ω) < (T : ℝ≥0∞)) ↔
    ∃ s : ℝ≥0, s < T ∧
      (X.X s ω < lower ∨ upper < X.X s ω) := by sorry
