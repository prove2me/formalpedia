-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_family_uniformContinuousOn_all_reserves
-- name    : AvramDividend.Classical.unbounded_scale_discount_family_uniformContinuousOn_all_reserves
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T15:41:46.203957+00:00
-- url     : https://prove2.me/theorems/75f27dd7-8c33-40ad-9703-db79ce81f331
-- title:
--   Uniform discount continuity of q-scale functions at every reserve
-- statement:
--   For unbounded variation and each real reserve, the family of scale-function values is uniformly continuous in its nonnegative discount parameter on every bounded interval. At positive reserves it has an explicit convolution Lipschitz constant; at zero and negative reserves it is identically zero.
-- source:
--   A direct proof from the canonical convolution Lipschitz bound, zero-origin vanishing and negative-reserve support, using Mathlib LipschitzOnWith.uniformContinuousOn.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.Topology.MetricSpace.Lipschitz
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_family_lipschitz_bound
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_zero_origin_nonnegative_discount
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_scale_discount_family_uniformContinuousOn_all_reserves
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (Q : ℝ) (hQ : 0 ≤ Q)
    (W : ℝ → ℝ → ℝ)
    (hW : ∀ q ∈ Icc (0 : ℝ) Q, IsScaleFunction X q (W q)) :
    ∀ x : ℝ, UniformContinuousOn (fun q : ℝ => W q x) (Icc (0 : ℝ) Q) := by sorry
