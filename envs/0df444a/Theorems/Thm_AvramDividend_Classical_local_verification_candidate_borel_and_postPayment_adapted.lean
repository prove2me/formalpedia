-- Prove2me | Theorems.Thm_AvramDividend_Classical_local_verification_candidate_borel_and_postPayment_adapted
-- name    : AvramDividend.Classical.local_verification_candidate_borel_and_postPayment_adapted
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T08:45:20.416216+00:00
-- url     : https://prove2.me/theorems/30325a04-ed29-4c0a-9ce9-4affb1d55962
-- title:
--   The HJB candidate is Borel measurable and its post-payment composition is adapted
-- statement:
--   Under the exact root HJB candidate assumptions, w is continuous on nonnegative reals and zero on negative reals. It may jump at zero, so ordinary global continuity is unavailable, but it is Borel measurable by measurable piecewise gluing along Ici 0 and Iio 0. The pinned theorem ContinuousOn.measurable_piecewise gives measurability from each region's continuous restriction. The previously Proved postPaymentReserve_cadlag_adapted gives adaptation of Uplus_t=x+X_t−D_{t+} to the right-continuous filtration. Compose its time-t measurable map with Measurable w to conclude Adapted F.rightCont (fun t ω=>w(Uplus_t)). This is essential for stopped terminal optional sampling, and correctly allows a boundary discontinuity at zero.
-- source:
--   Pinned ContinuousOn.measurable_piecewise exact type recovered from private signature probe f288e3e9..., and accepted postPaymentReserve_cadlag_adapted candidate 12129. No other Open imports.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_cadlag_adapted

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.local_verification_candidate_borel_and_postPayment_adapted
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0) :
    Measurable w ∧
      Adapted 𝓕.rightCont
        (fun t ω => w (x + X.X t ω - rightLimit D t ω)) := by sorry
