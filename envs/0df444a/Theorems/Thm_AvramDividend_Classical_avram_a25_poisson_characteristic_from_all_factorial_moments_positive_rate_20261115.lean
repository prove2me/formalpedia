-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a25_poisson_characteristic_from_all_factorial_moments_positive_rate_20261115
-- name    : AvramDividend.Classical.avram_a25_poisson_characteristic_from_all_factorial_moments_positive_rate_20261115
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T07:25:36.358123+00:00
-- url     : https://prove2.me/theorems/75dd29b9-9603-4156-b5c4-709bceebd420
-- title:
--   All descending factorial moments equal to rate powers imply exact Poisson characteristic function (strictly positive rate)
-- statement:
--   For any measurable natural-valued random variable on a probability space, if all descending factorial moments match r^n, the distribution is Poisson(r), therefore its real embedding has the characteristic function of the real-embedded Poisson(r) measure. A general abstract probability theorem independent of any Lévy process. Show E[(1+s)^K]=exp(rs) for s≥0 by nonnegative Tonelli and finite binomial expansion, then use uniqueness of MGF or PGF to identify the law. The strict positivity condition is essential: Lean's Bochner integral defaults to zero for non-integrable nonnegative factorial-moment functions, and the zero-rate version without integrability is invalid.
-- source:
--   General probability generating function uniqueness from all factorial moments and Tonelli, standard Poisson characterization.

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a25_poisson_characteristic_from_all_factorial_moments_positive_rate_20261115
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (r : ℝ≥0) (hr : 0 < r)
    (hMom : ∀ n : ℕ,
      (∫ ω, (Nat.descFactorial (K ω) n : ℝ) ∂P) = (r : ℝ) ^ n) :
    ∀ u : ℝ,
      charFun (P.map (fun ω => (K ω : ℝ))) u =
      charFun ((poissonMeasure r).map (fun n : ℕ => (n : ℝ))) u := by sorry
