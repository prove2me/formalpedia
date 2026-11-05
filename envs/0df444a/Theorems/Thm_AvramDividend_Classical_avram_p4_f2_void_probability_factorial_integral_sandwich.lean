-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f2_void_probability_factorial_integral_sandwich
-- name    : AvramDividend.Classical.avram_p4_f2_void_probability_factorial_integral_sandwich
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T00:28:23.6482+00:00
-- url     : https://prove2.me/theorems/517be7d8-2840-4004-afa7-4e0af58595f5
-- title:
--   Finite count first and factorial moments bound the probability of any jump
-- statement:
--   For a measurable Nat-valued count on a probability space with integrable first and second factorial moments, the probability of at least one occurrence lies between the expected count minus half its second factorial moment and the expected count. This integrates the certified pointwise Bonferroni estimate and is the core small-time void-probability comparison needed for original negative-band jump rates.
-- source:
--   Proved original X finite-band first and chronological pair rates c1e09ada and d938e9a5. Import Proved Bonferroni Nat helper e0ebc82d-7cf9-4f96-92f2-b94ac7474233. Intended downstream open original void slope 17372d7a.

import Mathlib
open MeasureTheory Set
noncomputable section

theorem AvramDividend.Classical.avram_p4_f2_void_probability_factorial_integral_sandwich
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hKm : Measurable K)
    (hFirst : Integrable (fun ω => (K ω : ℝ)) P)
    (hFactorial : Integrable
      (fun ω => (K ω : ℝ) * ((K ω : ℝ) - 1)) P) :
    (∫ ω, (K ω : ℝ) ∂P) -
        (∫ ω, (K ω : ℝ) * ((K ω : ℝ) - 1) ∂P) / 2 ≤
      P.real {ω : Ω | K ω ≠ 0} ∧
    P.real {ω : Ω | K ω ≠ 0} ≤
      (∫ ω, (K ω : ℝ) ∂P) := by sorry
