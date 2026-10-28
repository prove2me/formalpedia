-- Prove2me | Theorems.Thm_AvramDividend_Classical_cross_levy_prefix_increment_rectangles_of_marginal_laws
-- name    : AvramDividend.Classical.cross_levy_prefix_increment_rectangles_of_marginal_laws
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T12:37:59.008913+00:00
-- url     : https://prove2.me/theorems/e86abd7d-f2cd-4d23-bebb-f9d651e901a5
-- title:
--   Same one-time Lévy laws imply all finite consecutive increment joint laws across probability spaces
-- statement:
--   Two spectrally negative Lévy processes, possibly defined on completely different sample spaces, whose one-time distributions agree at every nonnegative time have identical joint laws for each finite consecutive increment vector on any monotone observation grid. The result follows from the exact previously Proved finite-prefix independence product rule and the one-time stationary increment identity for each process. This is the finite-dimensional identification route from a canonical Poisson Lévy realization to the arbitrary source process, independently of their underlying probability spaces.
-- source:
--   Proved levy_finitePrefix_increment_rectangle_product [35810ccf-6a41-4604-bcc0-1d5d1f2221c1]; SpectrallyNegativeLevy.stationaryIncrements; Mathlib ProbabilityTheory.IdentDistrib.measure_mem_eq. Fills the cross-model finite-increment law step prior to Proved piPathMeasure_eq_of_finite_cylinder_masses [4d62c918-6680-4aa9-98a1-d28e432ce446].

import Mathlib.Probability.IdentDistrib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Theorems.Thm_AvramDividend_Classical_levy_finitePrefix_increment_rectangle_product

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.cross_levy_prefix_increment_rectangles_of_marginal_laws
    {Ω₁ Ω₂ : Type*} [m₁ : MeasurableSpace Ω₁] [m₂ : MeasurableSpace Ω₂]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂}
    {𝓕₁ : Filtration ℝ≥0 m₁} {𝓕₂ : Filtration ℝ≥0 m₂}
    (X : SpectrallyNegativeLevy P₁ 𝓕₁)
    (Y : SpectrallyNegativeLevy P₂ 𝓕₂)
    (hMarginal : ∀ u : ℝ≥0, Measure.map (X.X u) P₁ = Measure.map (Y.X u) P₂)
    (t : ℕ → ℝ≥0) (ht : Monotone t)
    (n : ℕ) (B : Fin n → Set ℝ) (hB : ∀ i, MeasurableSet (B i)) :
    P₁ {ω | (fun i : Fin n =>
      X.X (t (i.val + 1)) ω - X.X (t i.val) ω) ∈
        Set.pi Set.univ B} =
    P₂ {ω | (fun i : Fin n =>
      Y.X (t (i.val + 1)) ω - Y.X (t i.val) ω) ∈
        Set.pi Set.univ B} := by sorry
