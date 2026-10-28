-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_family_continuousOn_all_reserves
-- name    : AvramDividend.Classical.unbounded_scale_discount_family_continuousOn_all_reserves
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T15:33:30.303923+00:00
-- url     : https://prove2.me/theorems/6c3d1923-dcc2-4dab-b50a-2d4d114f6f48
-- title:
--   Continuity in discount across every real reserve, including the origin and ruin region
-- statement:
--   For unbounded-variation spectrally negative Lévy processes and a compact nonnegative discount interval, the q-scale function depends continuously on q for every reserve x in the entire real line. Positive reserves use the proved convolution Lipschitz bound, negative reserves use the support condition Wq(x)=0, and x=0 uses the proved zero-origin result.
-- source:
--   Combine two canonical Proved theorems on discount continuity at positive reserves and zero-origin vanishing, with scale-function support at negative reserves.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.Topology.ContinuousOn
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_family_continuousOn
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_zero_origin_nonnegative_discount
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_scale_discount_family_continuousOn_all_reserves
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (Q : ℝ) (hQ : 0 ≤ Q)
    (W : ℝ → ℝ → ℝ)
    (hW : ∀ q ∈ Icc (0 : ℝ) Q, IsScaleFunction X q (W q)) :
    ∀ x : ℝ, ContinuousOn (fun q : ℝ => W q x) (Icc (0 : ℝ) Q) := by sorry
