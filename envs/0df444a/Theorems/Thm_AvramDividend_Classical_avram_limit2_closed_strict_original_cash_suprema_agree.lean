-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_closed_strict_original_cash_suprema_agree
-- name    : AvramDividend.Classical.avram_limit2_closed_strict_original_cash_suprema_agree
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:50:29.6153+00:00
-- url     : https://prove2.me/theorems/c2284f0f-4f3d-4bdd-a1d0-64283ca0820f
-- title:
--   Closed and positive strict original discounted dividend cash suprema agree exactly
-- statement:
--   For the genuine original Lévy process and admissible D, the supremum of discounted Stieltjes expected cash on paymentTimes(ruinTime) intersect closed integer Iic(n) equals the supremum along strict positive open Iio(n+1) horizons. The two independently Proved original dividendValue exhaustion results identify both sides with the same actual perpetual dividendValue. Individual horizon cash need not match: finite endpoint and time-zero atoms are retained by the limit. No equality-in-law, extra axiom or finite terminal assumption.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendValue_eq_iSup_truncated
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_strict_positive_integer_horizon_exhaustion

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_closed_strict_original_cash_suprema_agree
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissible X x D) :
    (⨆ n : ℕ,
      ∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) =
    (⨆ n : ℕ,
      ∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Iio (((n + 1 : ℕ) : ℝ)),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) := by sorry
