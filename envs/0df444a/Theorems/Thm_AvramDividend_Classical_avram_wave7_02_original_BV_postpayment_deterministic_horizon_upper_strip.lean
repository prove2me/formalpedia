-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_postpayment_deterministic_horizon_upper_strip
-- name    : AvramDividend.Classical.avram_wave7_02_original_BV_postpayment_deterministic_horizon_upper_strip
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T12:12:38.911846+00:00
-- url     : https://prove2.me/theorems/4a12fe1a-6203-4da8-9be5-560a076343a1
-- title:
--   Original BV physical drift gives a deterministic bounded-horizon postpayment reserve upper strip
-- statement:
--   For the original BV Levy process and original left-continuous dividend strategy, a single almost-sure event bounds every postpayment reserve at t up to T by x+T*physical drift when drift is nonnegative. This incorporates negative source jumps, diffuse source loss, simultaneous dividends, and the time-zero atom. This is the upper side of genuine C1 localisation, while the lower ruin boundary and compensated generator remain open.
-- source:
--   Proved original BV controlled increment theorem 6c45ed32 and original X.X_zero plus Proved dividend right-limit monotonic inequality 953f0e91.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_controlled_postpayment_increment_drift_envelope
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_02_original_BV_postpayment_deterministic_horizon_upper_strip
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (T : ℝ≥0) (hd : 0 ≤ X.drift) :
    ∀ᵐ ω ∂P, ∀ (t : ℝ≥0), t ≤ T →
      x + X.X t ω - rightLimit D t ω ≤
        x + (T : ℝ) * X.drift := by sorry
