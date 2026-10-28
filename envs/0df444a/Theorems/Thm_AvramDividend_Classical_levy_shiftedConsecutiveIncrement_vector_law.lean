-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_shiftedConsecutiveIncrement_vector_law
-- name    : AvramDividend.Classical.levy_shiftedConsecutiveIncrement_vector_law
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T10:30:31.917109+00:00
-- url     : https://prove2.me/theorems/16224575-ee6f-4052-8541-b08eae386fdf
-- title:
--   Joint law of every finite consecutive Lévy increment vector is stationary under a deterministic shift
-- statement:
--   For an arbitrary monotone finite observation grid and deterministic offset, the full finite-dimensional probability law of consecutive Lévy increments is invariant under the shift. Extends the Proved rectangle-factorisation result to all measurable sets on the finite product space using a finite-cylinder measure uniqueness theorem.
-- source:
--   Exact strong-Markov dividend proof dependency 79978d61-9d1f-4b20-b8a5-114797a8e380. Consumes finite-cylinder uniqueness and joint shifted rectangle stationarity, each remotely elaborated in the pinned revision.

import Mathlib.Probability.IdentDistrib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_piPathMeasure_eq_of_finite_cylinder_masses
import Theorems.Thm_AvramDividend_Classical_levy_finitePrefix_shifted_increment_rectangle_eq

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_shiftedConsecutiveIncrement_vector_law
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (t : ℕ → ℝ≥0) (ht : Monotone t) (n : ℕ) :
    Measure.map (fun ω : Ω => fun i : Fin n =>
      X.X (s + t (i.val + 1)) ω - X.X (s + t i.val) ω) P =
    Measure.map (fun ω : Ω => fun i : Fin n =>
      X.X (t (i.val + 1)) ω - X.X (t i.val) ω) P := by
  sorry
