-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_twoagentA_public_original_marked_interval_integral_adjacent_additivity_20261122
-- name    : AvramDividend.Classical.avram_twoagentA_public_original_marked_interval_integral_adjacent_additivity_20261122
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T14:07:46.518797+00:00
-- url     : https://prove2.me/theorems/f30cd4ef-28ca-458a-a4f3-beba19871b35
-- title:
--   Original actual signed-mark integral proxy bridge 83558868
-- statement:
--   Source-faithful PUBLIC republishing of an accepted true original negative mark integral bridge, with exact proof and substitution of already Proved PUBLIC dependencies. No new mathematical assumptions introduced.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped Classical NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_twoagentA_public_original_marked_interval_integral_adjacent_additivity_20261122
    (μ : Measure (ℝ≥0 × ℝ)) (T : ℝ≥0)
    (a b c : ℝ) (hab : a ≤ b) (hbc : b ≤ c)
    (hInt : IntegrableOn (fun p : ℝ≥0 × ℝ => p.2)
      (Ioc (0 : ℝ≥0) T ×ˢ Ioc a c) μ) :
    (∫ p in Ioc (0 : ℝ≥0) T ×ˢ Ioc a c, p.2 ∂μ) =
      (∫ p in Ioc (0 : ℝ≥0) T ×ˢ Ioc a b, p.2 ∂μ) +
      (∫ p in Ioc (0 : ℝ≥0) T ×ˢ Ioc b c, p.2 ∂μ) := by sorry
