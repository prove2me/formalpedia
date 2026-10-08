-- Prove2me | Theorems.Thm_AvramDividend_Classical_local_verification_smooth_differentiable
-- name    : AvramDividend.Classical.local_verification_smooth_differentiable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T07:16:01.740677+00:00
-- url     : https://prove2.me/theorems/8475af2e-29ad-4852-98bf-62460b864e98
-- title:
--   Both bounded-variation and unbounded-variation local-verification regularity assumptions imply interior differentiability
-- statement:
--   The exact smoothness disjunction in AvramDividend.Classical.local_verification gives C² regularity for unbounded-variation Lévy processes and C¹ regularity for bounded-variation processes on the positive interior below cap C. Either case yields ordinary differentiability on that region. This is the correct generic regularity fact required to apply the HJB derivative bound to finite dividend payments.
-- source:
--   Pinned Mathlib ContDiffOn.differentiableOn; exact hw_smooth assumption from local_verification.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.local_verification_smooth_differentiable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_smooth :
      (¬ X.BoundedVariation → ContDiffOn ℝ 2 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation → ContDiffOn ℝ 1 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})) :
    DifferentiableOn ℝ w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := by sorry
