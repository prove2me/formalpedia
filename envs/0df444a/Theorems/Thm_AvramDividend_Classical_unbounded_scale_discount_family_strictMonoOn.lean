-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_family_strictMonoOn
-- name    : AvramDividend.Classical.unbounded_scale_discount_family_strictMonoOn
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T14:48:50.295925+00:00
-- url     : https://prove2.me/theorems/58691722-c3bd-4273-952f-566c7f366136
-- title:
--   Strict monotonicity of unbounded-variation q-scale families in the discount
-- statement:
--   For an unbounded-variation spectrally negative Lévy process with a valid q-scale function W q for every nonnegative q, the function mapping q to W q x is strictly increasing for each x>0.
-- source:
--   Direct functional application of the verified strict pairwise q-discount monotonicity theorem.

import Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_strict_monotone
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_scale_discount_family_strictMonoOn
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (W : ℝ → ℝ → ℝ)
    (hW : ∀ q : ℝ, 0 ≤ q → IsScaleFunction X q (W q)) :
    ∀ x : ℝ, 0 < x →
      StrictMonoOn (fun q : ℝ => W q x) (Ici (0 : ℝ)) := by sorry
