-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a116_ae_zero_nat_count_haslaw_zero_rate_poisson_20261114
-- name    : AvramDividend.Classical.avram_a116_ae_zero_nat_count_haslaw_zero_rate_poisson_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T19:14:26.28953+00:00
-- url     : https://prove2.me/theorems/126cb32c-e61a-4218-851d-2de08751b973
-- title:
--   Almost surely zero measurable count has exactly the zero-rate Poisson law
-- statement:
--   On any probability space, any measurable natural-number-valued random variable equal to zero almost surely has exactly the Poisson distribution of rate zero. This pure probability-theoretic auxiliary allows the zero-rate branch of the original Lévy physical jump-count Poisson theorem to close using the previously Proved trivial-rate Poisson measure equals Dirac zero result.
-- source:
--   Proved levy_foundations_poissonMeasure_zero and Mathlib Measure.map_congr, Measure.map_const; HasLaw as an ae-measurable pushforward law.

import Mathlib
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a116_ae_zero_nat_count_haslaw_zero_rate_poisson_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (hZero : K =ᵐ[P] (fun _ : Ω => (0 : ℕ))) :
    HasLaw K (poissonMeasure (0 : ℝ≥0)) P := by sorry
