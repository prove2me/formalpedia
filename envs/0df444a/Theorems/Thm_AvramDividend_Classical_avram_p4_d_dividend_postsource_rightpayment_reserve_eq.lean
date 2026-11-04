-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_postsource_rightpayment_reserve_eq
-- name    : AvramDividend.Classical.avram_p4_d_dividend_postsource_rightpayment_reserve_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:56:08.362074+00:00
-- url     : https://prove2.me/theorems/4fb2f44f-7382-4ab2-8b4f-352ec4b3f189
-- title:
--   Original post-source prepayment reserve minus the exact right dividend equals postpayment reserve
-- statement:
--   For the genuine original Lévy source X and cumulative left-continuous dividend control D, at each path and time, the source state after the X jump but before the right dividend is x+X_t-D_t. Subtracting D_{t+}-D_t gives x+X_t-D_{t+}. Valid at time zero, simultaneous source/dividend jumps, cap contact, horizon and ruin, without a smoothness hypothesis.
-- source:
--   Original Avram dividend definition U_t=x+X_t-D_t and rightLimit D t; Eq. (5.13) ordering, pinned definition UUID 561c1e83-0505-4d9d-9f28-33943f44b28a.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_d_dividend_postsource_rightpayment_reserve_eq
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (t : ℝ≥0) :
    x + X.X t ω - rightLimit D t ω =
      riskProcess X x D t ω - (rightLimit D t ω - D t ω) := by sorry
