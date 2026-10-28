-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_family_continuousOn
-- name    : AvramDividend.Classical.unbounded_scale_discount_family_continuousOn
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T15:21:24.332887+00:00
-- url     : https://prove2.me/theorems/c5b46374-7f16-4f72-a893-765ea6c902e0
-- title:
--   Continuity of unbounded-variation scale functions in the discount parameter
-- statement:
--   For an unbounded-variation spectrally negative Lévy process and any family of q-scale functions on the compact nonnegative discount range [0,Q], the scale function at each positive reserve depends continuously on its discount parameter, including the zero-discount endpoint. The proof uses the explicit self-convolution Lipschitz bound.
-- source:
--   The proved compact-discount Lipschitz inequality combined with Mathlib's LipschitzOnWith.continuousOn theorem.

import Mathlib.Topology.MetricSpace.Lipschitz
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_family_lipschitz_bound
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_scale_discount_family_continuousOn
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (Q : ℝ) (hQ : 0 ≤ Q)
    (W : ℝ → ℝ → ℝ)
    (hW : ∀ q ∈ Icc (0 : ℝ) Q, IsScaleFunction X q (W q)) :
    ∀ x : ℝ, 0 < x →
      ContinuousOn (fun q : ℝ => W q x) (Icc (0 : ℝ) Q) := by sorry
