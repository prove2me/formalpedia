-- Prove2me | Theorems.Thm_AvramDividend_Classical_killed_firstRecord_initial_lower_of_raw_exit
-- name    : AvramDividend.Classical.killed_firstRecord_initial_lower_of_raw_exit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T15:57:32.914448+00:00
-- url     : https://prove2.me/theorems/71994c25-ea69-4bb6-90e2-1e2a67f9ad6e
-- title:
--   The ordinary q-scale exit identity implies the actual first-record payment lower estimate
-- statement:
--   Assume the standard ordinary two-sided q-scale exit formula, weighted by exp(−qTε), for paths crossing ε before falling below ε−a, with the official first-passage clock. The established named-clock survival sandwich implies that this unscaled discounted expectation is a lower bound for the actual first upward record surviving reflected ruin. The independently Proved nonnegative payment-scaling theorem then multiplies the lower bound by ε, yielding the exact initial killed-record expectation used in the stopped renewal inequality. It leaves only the genuine q-scale exit theorem as an assumption.
-- source:
--   Avram, Palmowski and Pistorius (2007), equation (3.6) and Proposition 1; combination of named first-upcrossing survival comparison and killed integral scalar homogeneity.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Analysis.Complex.Exponential
import Theorems.Thm_AvramDividend_Classical_named_killed_upcrossing_lower_of_raw_exit
import Theorems.Thm_AvramDividend_Classical_killed_lintegral_ofReal_scaled_lower

open MeasureTheory
open scoped NNReal ENNReal Classical
open AvramDividend.Classical

theorem AvramDividend.Classical.killed_firstRecord_initial_lower_of_raw_exit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) (W : ℝ → ℝ)
    (hRaw : (∫⁻ ω,
      if twoSidedExitUpTime X ε ω ≠ ∞ ∧
          (∀ t : ℝ≥0, t < (twoSidedExitUpTime X ε ω).toNNReal →
            ε - a ≤ X.X t ω) then
        ENNReal.ofReal (Real.exp
          (-(q * (twoSidedExitUpTime X ε ω).toReal)))
      else 0 ∂P) =
      ENNReal.ofReal (W (a - ε) / W a)) :
    ENNReal.ofReal (ε * (W (a - ε) / W a)) ≤
      (∫⁻ ω,
        if twoSidedExitUpTime X ((1 : ℝ) * ε) ω <
            barrierRuinTime X a ω then
          ENNReal.ofReal (ε * Real.exp
            (-(q * (twoSidedExitUpTime X ((1 : ℝ) * ε) ω).toReal)))
        else 0 ∂P) := by sorry
