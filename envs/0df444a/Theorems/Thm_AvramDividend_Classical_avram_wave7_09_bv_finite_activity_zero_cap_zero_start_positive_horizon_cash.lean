-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_09_bv_finite_activity_zero_cap_zero_start_positive_horizon_cash
-- name    : AvramDividend.Classical.avram_wave7_09_bv_finite_activity_zero_cap_zero_start_positive_horizon_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:52:20.637833+00:00
-- url     : https://prove2.me/theorems/09bbe99b-9773-470f-8348-ab31e25fb1c8
-- title:
--   Original BV zero-cap zero-start reflected strategy has positive finite-horizon Stieltjes cash under finite Lévy activity
-- statement:
--   In the exact original Standing bounded-variation spectrally negative Lévy model with finite total negative-jump activity, the canonical zero-barrier control started with x=0 and cap C=0 pays strictly positive expected discounted complete Stieltjes dividends by at least one natural finite horizon. Its payout uses the original ruinTime and paymentTimes including the initial atom. Consequently the zero-cap BV verification inequality with vacuous strict-interior HJB and w≡0 fails even when hxc and w0≥0 are added, under these existence hypotheses. This theorem itself certifies positive cash and does not claim unconditional existence of a Standing/BV source.
-- source:
--   Avram Dividend Classical canonical dividendMeasure, barrierStrategy and ruinTime. Derives from Proved bv_standing_drift_pos 0432f641; Proved bv_finite_activity_zero_reflected_first_jump_payout 6f73f927; Proved barrierValue_self_eq_barrierSupValue 11b589b7; Proved barrierStrategy_admissibleLe_nonnegative_barrier 32b4ccb8; and Proved dividendValue_le_of_uniform_truncated_bounds dc933bd8. This sharpens the conditional legacy C=0 counterexample c4bc3559 to x=0 with hxc, finite positive horizon, and finite Lévy activity, without a surrogate process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_09_bv_finite_activity_zero_cap_zero_start_positive_horizon_cash
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (hq : 0 < q) :
    ∃ n : ℕ, 0 <
      (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X 0 (barrierStrategy X 0 0) ω) ∩ Iic (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure (barrierStrategy X 0 0) ω) ∂P) := by sorry
