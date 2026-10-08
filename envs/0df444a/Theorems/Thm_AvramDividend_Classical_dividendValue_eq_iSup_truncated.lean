-- Prove2me | Theorems.Thm_AvramDividend_Classical_dividendValue_eq_iSup_truncated
-- name    : AvramDividend.Classical.dividendValue_eq_iSup_truncated
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T10:01:58.550297+00:00
-- url     : https://prove2.me/theorems/3b737955-7611-4616-acb5-10f4f8025612
-- title:
--   Dividend value is the supremum of deterministic-horizon truncated values
-- statement:
--   For an admissible dividend strategy, its full expected discounted dividend value equals the increasing supremum of the same Stieltjes integral truncated at deterministic integer horizons. The payment-time set is exhausted by its intersections with (-infinity,n]. This isolates the measurability and monotone-convergence step from the stochastic Ito estimate.
-- source:
--   Measure-theoretic limiting step in the proof of Avram-Palmowski-Pistorius Proposition 4(i), pp. 18-19, where finite stopped estimates pass to the full dividend integral by monotone convergence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.dividendValue_eq_iSup_truncated
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissible X x D) :
    dividendValue X q x D =
      ⨆ n : ℕ,
        ∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (n : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P := by sorry
