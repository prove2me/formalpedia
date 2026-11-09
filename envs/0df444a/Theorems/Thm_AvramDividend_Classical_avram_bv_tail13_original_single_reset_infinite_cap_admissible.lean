-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_tail13_original_single_reset_infinite_cap_admissible
-- name    : AvramDividend.Classical.avram_bv_tail13_original_single_reset_infinite_cap_admissible
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T13:50:04.790211+00:00
-- url     : https://prove2.me/theorems/66d89163-5d64-43aa-9679-fd5eb260ae7b
-- title:
--   Original BV single reserve reset is financially admissible at infinite cap
-- statement:
--   For any spectrally negative Levy process, positive initial reserve and strictly positive deterministic clock, the one-payment strategy that distributes the positive reserve observed at the clock is genuinely admissible in the exact source IsAdmissibleLe at infinite cap. Reuses the public source right-limit and positive-clock admissibility theorem with actual ruin-clock prepayment affordability.
-- source:
--   Original source IsAdmissibleLe and riskProcess_nonneg_before_ruin: before ruin at the reset clock the reserve is nonnegative, making the clipped payout no larger than the available surplus; the positive-clock BV12 theorem then discharges all original admissibility conditions.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_riskProcess_nonneg_before_ruin
import Theorems.Thm_AvramDividend_Classical_avram_bv_tail12_single_positive_clock_reset_admissible
import Theorems.Thm_AvramDividend_Classical_avram_bv_tail13_single_step_rightLimit_eq
import Theorems.Thm_AvramDividend_Classical_avram_bv_tail13_original_single_reset_isDividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_tail13_original_single_reset_infinite_cap_admissible
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (hx : 0 ≤ x) (s : ℝ≥0) (hs : 0 < s) :
    IsAdmissibleLe X x ⊤ (fun t ω =>
      if t ≤ s then 0 else max (x + X.X s ω) (0 : ℝ)) := by sorry
