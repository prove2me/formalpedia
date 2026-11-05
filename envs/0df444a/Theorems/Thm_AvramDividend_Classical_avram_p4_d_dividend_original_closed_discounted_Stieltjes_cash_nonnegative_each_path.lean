-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_closed_discounted_Stieltjes_cash_nonnegative_each_path
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_closed_discounted_Stieltjes_cash_nonnegative_each_path
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T01:15:45.323192+00:00
-- url     : https://prove2.me/theorems/0659c504-4251-4183-9bc5-14e0377edc62
-- title:
--   Actual original stopped closed discounted Stieltjes Cash is nonnegative on every path
-- statement:
--   For the canonical original spectrally negative Lévy reserve, controlled ruinTime, dividendMeasure and the P4-F closed discounted paymentTimes intersection through the finite stop, the real value of the ENNReal lintegral is nonnegative on every source path. Includes valid time-zero and right-horizon atoms and supports increasing-horizon value bounds.
-- source:
--   Canonical original P4-F Cash exact physical definition and pinned Mathlib ENNReal.toReal_nonneg.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_closed_discounted_Stieltjes_cash_nonnegative_each_path
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (q : ℝ) (τ : Ω → ℝ≥0) (Cash : Ω → ℝ)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal) :
    ∀ ω, 0 ≤ Cash ω := by sorry
