-- Prove2me | Theorems.Thm_AvramDividend_Classical_continuousOn_zero_of_ae_zero_restrict_Ioo
-- name    : AvramDividend.Classical.continuousOn_zero_of_ae_zero_restrict_Ioo
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T10:55:14.027917+00:00
-- url     : https://prove2.me/theorems/19401bb4-52b7-4a9d-a135-c99e93242cb8
-- title:
--   A continuous function a.e.-zero on a positive open interval vanishes pointwise
-- statement:
--   A function continuous on (0,a) and almost-everywhere zero under Lebesgue measure restricted to that interval is zero at every state x in the interval. Each x belongs to the support of restricted Lebesgue measure, because the interval is open and unrestricted Lebesgue measure has full support. Use the proved local continuity-at-support zero lemma.
-- source:
--   Pinned Mathlib neighbourhood, support and compact interval continuity theorems; Avram Dividend generator residual localisation.

import Mathlib

open MeasureTheory Set Filter
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem continuousOn_zero_of_ae_zero_restrict_Ioo
    (f : ℝ → ℝ) (a : ℝ)
    (hcont : ContinuousOn f (Ioo 0 a))
    (hae : ∀ᵐ x ∂((volume : Measure ℝ).restrict (Ioo 0 a)),
      f x = 0) :
    ∀ x ∈ Ioo 0 a, f x = 0 := by sorry

end AvramDividend.Classical
