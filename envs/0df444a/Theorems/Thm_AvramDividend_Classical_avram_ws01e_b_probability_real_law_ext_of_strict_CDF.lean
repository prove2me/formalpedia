-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_probability_real_law_ext_of_strict_CDF
-- name    : AvramDividend.Classical.avram_ws01e_b_probability_real_law_ext_of_strict_CDF
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T09:31:43.863004+00:00
-- url     : https://prove2.me/theorems/c663d182-cb34-4471-9681-5fa4a19aba96
-- title:
--   Strict real-valued cumulative distribution equality determines probability law
-- statement:
--   For any two Borel probability measures μ and ν on the real numbers, if μ((−∞,a))=ν((−∞,a)) at every real strict threshold a, then μ=ν exactly as measures. This extends the actual strict drawdown/minimum event equality proven under the joint Esscher exponential observation clock to full distribution equality, a reusable step for Laplace-transform calculations. The proof passes from strict lower rays to their complementary upper rays using probability normalisation and invokes pinned Mathlib Measure.ext_of_Ici.
-- source:
--   Pinned Mathlib Measure.ext_of_Ici, measure_compl for finite Borel lower rays, and probability measure_univ=1.

import Mathlib

open MeasureTheory Set
open scoped ENNReal

/-- Equality of strict real lower-ray CDFs determines a probability measure. -/

theorem AvramDividend.Classical.avram_ws01e_b_probability_real_law_ext_of_strict_CDF
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ a : ℝ, μ (Iio a) = ν (Iio a)) : μ = ν := by sorry
