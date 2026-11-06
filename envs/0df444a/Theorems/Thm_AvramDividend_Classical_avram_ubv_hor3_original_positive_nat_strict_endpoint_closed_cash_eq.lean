-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_positive_nat_strict_endpoint_closed_cash_eq
-- name    : AvramDividend.Classical.avram_ubv_hor3_original_positive_nat_strict_endpoint_closed_cash_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T14:13:21.91172+00:00
-- url     : https://prove2.me/theorems/26471312-1ac7-4e0c-aedf-b5d836f24549
-- title:
--   Exact original positive natural-clock stopped Stieltjes cash excludes the natural-horizon atom
-- statement:
--   For every original Levy X, actual dividend D, positive natural clipping n and any real closed time horizon T, the expected original discounted Stieltjes cash under min(ruinTime,n) equals the cash under genuine ruinTime restricted to t<n and t≤T. The equality retains the initial t=0 dividend atom, excludes a possible jump at the natural endpoint t=n, and makes no assumptions about martingale centring or payout integrability.
-- source:
--   Direct source-exact reduction using the Proved paymentTimes_min_ofReal_eq_inter_Iio_of_pos theorem and pinned ENNReal.ofReal_natCast; the inner Stieltjes measure and original probability P are unchanged. Independent of d457be6b, 665b3b52, fdb9a6a3 and 0dda1be7.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_min_ofReal_eq_inter_Iio_of_pos
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem AvramDividend.Classical.avram_ubv_hor3_original_positive_nat_strict_endpoint_closed_cash_eq
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (q T : ℝ) (n : ℕ) (hn : 0 < n) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) =
    (∫⁻ ω, ∫⁻ t in (paymentTimes (ruinTime X x D ω) ∩ Iio (n : ℝ)) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) := by sorry
