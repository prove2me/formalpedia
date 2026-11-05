-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_strict_survival_terminal_eq_postpayment_book
-- name    : AvramDividend.Classical.avram_p3_c_bvchain_original_strict_survival_terminal_eq_postpayment_book
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T08:42:34.088175+00:00
-- url     : https://prove2.me/theorems/e7de115e-f688-43c0-b03c-960603f4e767
-- title:
--   Original BV strict-survival discounted postpayment terminal equals canonical source expression
-- statement:
--   For the actual original process X, dividend strategy D and a nonnegative horizon T, the discounted post-rightpayment w evaluated at the book reserve minus the right-payment is identically the canonical P3 post-rightLimit reserve. The equality is under the exact strict-survival indicator, including the zero terminal when ruin has occurred. No new regularity, integrability or stochastic assumption is required.
-- source:
--   Original controlled riskProcess := x + X.X - D and original left-continuous/rightpayment dividendStrategy definitions in 561c1e83-0505-4d9d-9f28-33943f44b28a; exact main P3 9cd69d89-505f-476c-b105-83c6970f7843 terminal convention.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p3_c_bvchain_original_strict_survival_terminal_eq_postpayment_book
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ)
    (ω : Ω) (q T : ℝ) (hT : 0 ≤ T) :
    let S : ℝ≥0 := ⟨T, hT⟩
    (if (S : ℝ≥0∞) < ruinTime X x D ω then
       Real.exp (-(q * T)) *
         w (riskProcess X x D S ω - (rightLimit D S ω - D S ω))
     else 0) =
    (if (S : ℝ≥0∞) < ruinTime X x D ω then
       Real.exp (-(q * T)) * w (x + X.X S ω - rightLimit D S ω)
     else 0) := by sorry
