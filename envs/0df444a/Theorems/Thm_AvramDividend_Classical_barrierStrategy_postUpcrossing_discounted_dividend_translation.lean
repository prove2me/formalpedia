-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_postUpcrossing_discounted_dividend_translation
-- name    : AvramDividend.Classical.barrierStrategy_postUpcrossing_discounted_dividend_translation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T10:35:46.209157+00:00
-- url     : https://prove2.me/theorems/a6b696cb-e838-4831-807f-4e128fc2f6be
-- title:
--   Post-upcrossing discounted Stieltjes dividends translate to shifted Lévy supremum measure
-- statement:
--   After a finite first upward barrier passage, the discounted Stieltjes dividends strictly after the passage equal the first-passage discount factor times the discounted Stieltjes dividends of the shifted Lévy running-supremum path at strictly positive relative times. Uses the previously proved dividend-measure map identity and discounted lintegral translation. Explicitly assumes the shifted supremum Stieltjes measure has no mass on nonpositive real times; the old barrier measure automatically satisfies this and both measures are locally finite. This is a non-stopped payoff-translation precursor of the strong-Markov barrier valuation theorem, with the actual stopped ruin window still to be handled.
-- source:
--   Proved source lemmas 3093890e-4ed7-4198-8491-5f41d268763c and 4c583263-f38b-4e14-bc95-07738e938d75; Avram, Palmowski and Pistorius (2007) barrier valuation Proposition 1.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_dividendMeasure_map_shift_of_support
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_dividendMeasure_zero_nonpositive
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_locallyFinite
import Theorems.Thm_AvramDividend_Classical_lintegral_killed_discount_translation_of_measure_map
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.barrierStrategy_postUpcrossing_discounted_dividend_translation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (q : ℝ) (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞)))
    (hνneg : (dividendMeasure
      (fun r (_ : Ω) =>
        sSup ((fun v : ℝ≥0 => X.X (u + v) ω - X.X u ω) '' Set.Icc 0 r))
      ω) (Set.Iic (0 : ℝ)) = 0) :
    (∫⁻ t in Set.Ioi (u : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
      ∂(dividendMeasure (barrierStrategy X x a) ω)) =
    ENNReal.ofReal (Real.exp (-(q * (u : ℝ)))) *
      (∫⁻ t in Set.Ioi (0 : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure
      (fun r (_ : Ω) =>
        sSup ((fun v : ℝ≥0 => X.X (u + v) ω - X.X u ω) '' Set.Icc 0 r))
      ω)) := by sorry
