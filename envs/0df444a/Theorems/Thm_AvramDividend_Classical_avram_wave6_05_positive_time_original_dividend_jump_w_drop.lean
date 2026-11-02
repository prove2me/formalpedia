-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_05_positive_time_original_dividend_jump_w_drop
-- name    : AvramDividend.Classical.avram_wave6_05_positive_time_original_dividend_jump_w_drop
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T19:29:19.882226+00:00
-- url     : https://prove2.me/theorems/ae7cd7bc-a0a8-4602-bcbd-2d743f9b670b
-- title:
--   Positive-time original simultaneous-source-and-dividend payment has w-drop at least the cash atom
-- statement:
--   For the actual spectrally negative Levy path and every capped admissible dividend strategy at each strictly positive time before ruin, the post-source and pre-dividend reserve is bounded above by C and the post-dividend reserve is nonnegative. The full-cap endpoint secant inequality for w then shows w(prepayment)-w(postpayment) is at least the actual right dividend atom. The original source X_t already includes its left jump before any right dividend payment, so simultaneous source and dividend jumps are ordered correctly. At time zero the capped condition does not apply; use the separately Proved global cap-linear extension V for time-zero payments.
-- source:
--   Avram classical dividend control: IsAdmissibleLe caps the true riskProcess only at t>0; IsAdmissible imposes no overpayment before ruin; the Proved full-cap secant supplies the value drop including reserve-zero and cap endpoints.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_full_cap_gradient_secant
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave6_05_positive_time_original_dividend_jump_w_drop
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0) (ht : 0 < t)
    (hPre : (t : ℝ≥0∞) < ruinTime X x D ω) :
    rightLimit D t ω - D t ω ≤
      w (riskProcess X x D t ω) -
        w (riskProcess X x D t ω -
          (rightLimit D t ω - D t ω)) := by sorry
