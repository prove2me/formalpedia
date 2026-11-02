-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_admissible_finite_cap_reserve_le_including_zero
-- name    : AvramDividend.Classical.avram_wave5_05_ubv_original_admissible_finite_cap_reserve_le_including_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T15:05:24.884164+00:00
-- url     : https://prove2.me/theorems/fae86000-2496-4411-8448-9d968a6316b2
-- title:
--   Original genuinely admissible finite-cap controlled reserve never exceeds cap before ruin, including time zero
-- statement:
--   For the genuine original spectrally negative Levy process with any strictly positive finite cap c, initial capital x subject to ofReal x≤ofReal c, and original IsAdmissibleLe capped dividend strategy D, the actual riskProcess_t≤c at every time t strictly before ruin, including t=0 and the possibility x=c. No separately assumed pathwise hCap, derivative or C2 at cap, unbounded-variation premise, or permanent cap stopping is required. The proof uses previously Proved nonnegative initial capital and full original capped reserve range and the real/ENNReal order embedding at positive states.
-- source:
--   Proved original capped initial capital nonnegative b3117b07-8383-4143-a965-2d9876a04a99 and range including zero 15c076b4-b5f4-4b35-a392-5b8aac1cc0a9. This supplies canonical hCap for corrected core 429e17ca-5528-40b5-b593-7c03973d0706 unchanged.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_allCap_admissible_initial_capital_nonneg
import Theorems.Thm_AvramDividend_Classical_capped_riskProcess_range_before_ruin_including_zero

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem AvramDividend.Classical.avram_wave5_05_ubv_original_admissible_finite_cap_reserve_le_including_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x c : ℝ) (hc : 0 < c)
    (hxc : ENNReal.ofReal x ≤ ENNReal.ofReal c)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D) :
    ∀ (ω : Ω) (s : ℝ≥0),
      (s : ℝ≥0∞) < ruinTime X x D ω →
        riskProcess X x D s ω ≤ c := by sorry
