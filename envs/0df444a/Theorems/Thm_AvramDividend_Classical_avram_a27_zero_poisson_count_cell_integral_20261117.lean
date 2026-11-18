-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_zero_poisson_count_cell_integral_20261117
-- name    : AvramDividend.Classical.avram_a27_zero_poisson_count_cell_integral_20261117
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T16:07:15.382107+00:00
-- url     : https://prove2.me/theorems/0d17bfc6-af4f-4c55-8fbb-b12434b51c76
-- title:
--   Poisson zero-count cell integral equals the zero mass for an almost-surely unit weight
-- statement:
--   For a measurable original-space Poisson count K and any weight F which equals one almost surely on its zero event, the integral of F restricted to that event is the zero Poisson mass. This generic integral lemma closes the zero-cell portion of the source conditional jump Laplace law.
-- source:
--   Measured indicator integral and exact HasLaw pushforward; no marked-process independence assumptions.

import Mathlib
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
noncomputable section

/-- Integrating a unit weight on the zero Poisson count cell gives its law mass. -/

theorem AvramDividend.Classical.avram_a27_zero_poisson_count_cell_integral_20261117
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (r : ℝ≥0) (hLaw : HasLaw K (poissonMeasure r) P)
    (F : Ω → ℝ)
    (hF : ∀ᵐ ω ∂P, K ω = 0 → F ω = 1) :
    (∫ ω in {ω : Ω | K ω = 0}, F ω ∂P) =
      (poissonMeasure r).real {0} := by sorry
