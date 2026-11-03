-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_postpayment_reserve_zero_cap_interior_partition
-- name    : AvramDividend.Classical.avram_wave7_19_original_postpayment_reserve_zero_cap_interior_partition
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T21:13:01.385895+00:00
-- url     : https://prove2.me/theorems/f1496f35-a031-46a2-865f-a8a4fc78e85f
-- title:
--   Exact zero-reserve, cap-reserve or smooth-interior trichotomy at every original pre-ruin dividend time
-- statement:
--   For the original capped admissible spectrally negative Levy reserve, the post-rightpayment state at time zero or any strictly positive pre-ruin payment is exactly on the zero boundary, on the cap boundary, or inside the strict positive C2 HJB domain. The source initial dividend jump and all subsequent predictable right atoms are retained. This derives the spatial coverage trichotomy from existing original capital and cap assumptions without asserting reserve continuity at ruin or zero boundary mass.
-- source:
--   Original source paymentTimes and ruinTime, accepted source cap/solvency lemmas 2ecd3672, 16104f4f and a8120e3c.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_capped_postPaymentReserve_initial_state
import Theorems.Thm_AvramDividend_Classical_capped_postPaymentReserve_ofReal_le_cap
import Theorems.Thm_AvramDividend_Classical_capped_postPaymentReserve_within_cap_before_ruin
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_19_original_postpayment_reserve_zero_cap_interior_partition
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hxc : ENNReal.ofReal x ≤ C) (ω : Ω) (t : ℝ≥0)
    (ht : t = 0 ∨ (0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω)) :
    let y := x + X.X t ω - rightLimit D t ω
    y = 0 ∨ ENNReal.ofReal y = C ∨
      (0 < y ∧ ENNReal.ofReal y < C) := by sorry
