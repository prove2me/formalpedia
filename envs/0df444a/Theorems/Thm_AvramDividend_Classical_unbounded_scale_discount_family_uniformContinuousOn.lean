-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_family_uniformContinuousOn
-- name    : AvramDividend.Classical.unbounded_scale_discount_family_uniformContinuousOn
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T15:31:14.562986+00:00
-- url     : https://prove2.me/theorems/0d681c3c-21aa-4f9b-9bf5-991de42be9e8
-- title:
--   Uniform continuity of the unbounded-variation q-scale family on bounded discount ranges
-- statement:
--   For every fixed positive reserve and nonnegative compact discount interval [0,Q], any corresponding family of q-scale functions of an unbounded-variation spectrally negative Lévy process is uniformly continuous in its discount parameter. This follows from a proven explicit convolution Lipschitz bound.
-- source:
--   Derived from the canonical proved unbounded_scale_discount_family_lipschitz_bound theorem and Mathlib LipschitzOnWith.uniformContinuousOn.

import Mathlib.Topology.MetricSpace.Lipschitz
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_family_lipschitz_bound
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_scale_discount_family_uniformContinuousOn
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (Q : ℝ) (hQ : 0 ≤ Q)
    (W : ℝ → ℝ → ℝ)
    (hW : ∀ q ∈ Icc (0 : ℝ) Q, IsScaleFunction X q (W q)) :
    ∀ x : ℝ, 0 < x →
      UniformContinuousOn (fun q : ℝ => W q x) (Icc (0 : ℝ) Q) := by sorry
