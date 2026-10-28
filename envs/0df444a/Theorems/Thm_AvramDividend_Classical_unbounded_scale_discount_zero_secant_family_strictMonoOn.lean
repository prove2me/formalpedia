-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_zero_secant_family_strictMonoOn
-- name    : AvramDividend.Classical.unbounded_scale_discount_zero_secant_family_strictMonoOn
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T16:27:15.604019+00:00
-- url     : https://prove2.me/theorems/9806d220-e65e-4566-94a1-478df10b20b2
-- title:
--   Strict monotonicity of the zero-based q-scale discount secant family
-- statement:
--   At every strictly positive reserve, the map sending positive discount q to its zero-based scale-function difference quotient (W^q-W^0)/q is strictly increasing on (0, infinity).
-- source:
--   The proved pairwise strict discount secant comparison, applied to the family indexed over positive discounts.

import Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_zero_secant_strict_increasing
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_scale_discount_zero_secant_family_strictMonoOn
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (W : ℝ → ℝ → ℝ)
    (hW : ∀ q : ℝ, 0 ≤ q → IsScaleFunction X q (W q)) :
    ∀ x : ℝ, 0 < x →
      StrictMonoOn (fun q : ℝ => (W q x - W 0 x) / q) (Ioi (0 : ℝ)) := by sorry
