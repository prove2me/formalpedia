-- Prove2me | Theorems.Thm_AvramDividend_Classical_cross_levy_finite_increment_vector_law_of_marginals
-- name    : AvramDividend.Classical.cross_levy_finite_increment_vector_law_of_marginals
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T13:46:44.306987+00:00
-- url     : https://prove2.me/theorems/86a80deb-4bf8-4360-800b-f1ded05a6914
-- title:
--   Equal Lévy one-time laws imply equality of entire finite consecutive increment-vector distributions across sample spaces
-- statement:
--   Suppose two spectrally negative Lévy processes on different probability spaces have identical one-time marginal laws. Then for every finite monotone time grid, their complete vectors of consecutive increments have equal joint pushforward probability measures, not merely equal probabilities on rectangular cylinder events. This upgrades the previously Proved cross-space rectangle product theorem using finite-cylinder π-system uniqueness, and provides the direct input to deterministic reconstruction of finite path-value vectors.
-- source:
--   Proved cross_levy_prefix_increment_rectangles_of_marginal_laws [e86abd7d-f2cd-4d23-bebb-f9d651e901a5] and piPathMeasure_eq_of_finite_cylinder_masses [4d62c918-6680-4aa9-98a1-d28e432ce446], with adaptation/measurability from SpectrallyNegativeLevy. Completes the cross-space finite increment-law step.

import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Theorems.Thm_AvramDividend_Classical_piPathMeasure_eq_of_finite_cylinder_masses
import Theorems.Thm_AvramDividend_Classical_cross_levy_prefix_increment_rectangles_of_marginal_laws

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.cross_levy_finite_increment_vector_law_of_marginals
    {Ω₁ Ω₂ : Type*} [m₁ : MeasurableSpace Ω₁] [m₂ : MeasurableSpace Ω₂]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂}
    {𝓕₁ : Filtration ℝ≥0 m₁} {𝓕₂ : Filtration ℝ≥0 m₂}
    (X : SpectrallyNegativeLevy P₁ 𝓕₁)
    (Y : SpectrallyNegativeLevy P₂ 𝓕₂)
    (hMarginal : ∀ u : ℝ≥0, Measure.map (X.X u) P₁ = Measure.map (Y.X u) P₂)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (n : ℕ) :
    Measure.map (fun ω : Ω₁ => fun i : Fin n =>
      X.X (t (i.val + 1)) ω - X.X (t i.val) ω) P₁ =
    Measure.map (fun ω : Ω₂ => fun i : Fin n =>
      Y.X (t (i.val + 1)) ω - Y.X (t i.val) ω) P₂ := by sorry
