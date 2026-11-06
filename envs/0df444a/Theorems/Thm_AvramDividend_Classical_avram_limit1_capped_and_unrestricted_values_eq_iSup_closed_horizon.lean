-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit1_capped_and_unrestricted_values_eq_iSup_closed_horizon
-- name    : AvramDividend.Classical.avram_limit1_capped_and_unrestricted_values_eq_iSup_closed_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T23:55:59.955538+00:00
-- url     : https://prove2.me/theorems/b1923ae2-2486-46d8-8c39-66f20579a9b5
-- title:
--   Capped and unrestricted value equal the suprema of original closed integer-horizon dividend-measure rewards
-- statement:
--   The actual capped and unrestricted value functions equal the suprema, over their original admissible strategies, of expected discounted original dividendMeasure rewards over paymentTimes (ruinTime) intersected with the closed integer time horizon Iic n. This follows exactly from the Proved original dividendValue_eq_iSup_truncated theorem, once for IsAdmissibleLe through its original IsAdmissible component and once for unrestricted IsAdmissible, with two index congruences in each case. The closed horizon includes an atom at time zero and any right-time dividend at the terminal integer; no unjustified switch to Iio is made.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendValue_eq_iSup_truncated

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit1_capped_and_unrestricted_values_eq_iSup_closed_horizon
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (C : ℝ≥0∞) (x : ℝ) :
    (valueFunctionLe X q C x =
      ⨆ D : ℝ≥0 → Ω → ℝ, ⨆ hD : IsAdmissibleLe X x C D, ⨆ n : ℕ,
        (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (n : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω) ∂P)) ∧
    (valueFunction X q x =
      ⨆ D : ℝ≥0 → Ω → ℝ, ⨆ hD : IsAdmissible X x D, ⨆ n : ℕ,
        (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (n : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω) ∂P)) := by sorry
