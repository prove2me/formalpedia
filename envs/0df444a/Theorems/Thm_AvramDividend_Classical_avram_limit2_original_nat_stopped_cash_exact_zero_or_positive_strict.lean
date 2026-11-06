-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_original_nat_stopped_cash_exact_zero_or_positive_strict
-- name    : AvramDividend.Classical.avram_limit2_original_nat_stopped_cash_exact_zero_or_positive_strict
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T18:05:24.045469+00:00
-- url     : https://prove2.me/theorems/32454533-8fd0-4977-8dd0-1809217eb5fb
-- title:
--   Original natural stopped discounted dividend cash is exactly the initial atom at zero and strict pre-horizon cash for positive clocks
-- statement:
--   The actual original paymentTimes(min(ruinTime,n)) expected discounted Stieltjes cash has an exact by-cases characterization at every natural clock n. At n=0 it equals the singleton-time-zero dividendMeasure atom, with no disappearance. At n>0 it equals paymentTimes(ruinTime) ∩ Iio(n:ℝ), excluding payment at right endpoint n. Both branches import independent Proved/public original-process equalities 0f6cae65 and f083a162; no stochastic, integrability or equality-in-law hypothesis is added. This explicit statement resolves the original UBV positive-clock / zero-clock interface exactly.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_zero_clock_cash_eq_initial_atom
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_strict_horizon_cash_eq_natural_ruin_stop
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_original_nat_stopped_cash_exact_zero_or_positive_strict
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) :
    ∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) =
      if n = 0 then
        (∫⁻ ω, ∫⁻ t in ({0} : Set ℝ),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω) ∂P)
      else
        (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Set.Iio (n : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω) ∂P) := by sorry
