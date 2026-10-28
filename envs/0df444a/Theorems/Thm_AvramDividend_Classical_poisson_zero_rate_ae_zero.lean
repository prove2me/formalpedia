-- Prove2me | Theorems.Thm_AvramDividend_Classical_poisson_zero_rate_ae_zero
-- name    : AvramDividend.Classical.poisson_zero_rate_ae_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T07:41:38.3604+00:00
-- url     : https://prove2.me/theorems/dee005a3-1c7c-4086-b666-49d556eb2cbb
-- title:
--   A zero-rate Poisson piece has no arrivals almost surely
-- statement:
--   Any natural-valued random count whose law is Poisson with mean zero is almost surely zero. Show that the zero-intensity Poisson measure equals a Dirac mass at zero using its singleton probabilities, then apply HasLaw.ae_eq_of_dirac. This prevents zero-mass partition pieces, whose dummy point laws can have time atoms, from generating active marks in the canonical Poisson construction.
-- source:
--   Mathlib.Probability.Distributions.Poisson.Basic: poissonMeasure_singleton, Measure.ext_of_singleton, HasLaw.ae_eq_of_dirac; LeanLevy PoissonPointFamily zero-mass fallback.

import Mathlib

open ProbabilityTheory MeasureTheory
open scoped ENNReal

theorem AvramDividend.Classical.poisson_zero_rate_ae_zero
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (K : Ω → ℕ)
    (hK : HasLaw K (poissonMeasure 0) P) :
    ∀ᵐ ω ∂P, K ω = 0 := by sorry
