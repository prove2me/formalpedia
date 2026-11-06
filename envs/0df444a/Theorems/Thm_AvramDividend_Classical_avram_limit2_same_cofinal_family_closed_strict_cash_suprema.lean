-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_same_cofinal_family_closed_strict_cash_suprema
-- name    : AvramDividend.Classical.avram_limit2_same_cofinal_family_closed_strict_cash_suprema
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:52:47.079359+00:00
-- url     : https://prove2.me/theorems/30079144-a9d6-4b22-b071-169925d5f62a
-- title:
--   Original closed and open discounted cash suprema agree on the same nonmonotone cofinal family
-- statement:
--   For an arbitrary real deterministic cofinal horizon family T (not necessarily monotone), the suprema of genuine original ruin-stopped discounted Stieltjes cash on Iic(T k) and Iio(T k) agree. Ordinary cofinality implies strict cofinality by applying it at a+1, and two already Proved genuine original value exhaustion theorems equate both to the same full dividendValue. Time-zero/finite right-horizon atoms are retained in the suprema; no equality of finite-horizon Iio/Iic cash is asserted.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_arbitrary_cofinal_closed_horizon_exhaustion
import Theorems.Thm_AvramDividend_Classical_avram_limit2_arbitrary_strict_cofinal_horizon_exhaustion

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_same_cofinal_family_closed_strict_cash_suprema
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissible X x D)
    (T : ℕ → ℝ) (hT : ∀ a : ℝ, ∃ k : ℕ, a ≤ T k) :
    (⨆ k : ℕ,
      ∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (T k),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) =
    (⨆ k : ℕ,
      ∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T k),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) := by sorry
