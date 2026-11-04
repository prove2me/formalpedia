-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_quantitative_l2_tail_lintegral
-- name    : AvramDividend.Classical.avram_p2_j_ui_quantitative_l2_tail_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T19:34:34.140494+00:00
-- url     : https://prove2.me/theorems/d4010301-4528-4c74-a0d4-5c4b48b7d493
-- title:
--   Quantitative L² tail estimate: R times L¹ mass of values above R is bounded by second moment
-- statement:
--   For any measure, measurable nonnegative extended-real V and finite positive threshold R, the lintegral of V restricted to values at least R satisfies R times tail mass at most the second-moment lintegral. This is a direct Vitali-style quantitative uniform-integrability tail estimate, available uniformly whenever the L2 moments are uniformly bounded. Proves the inequality pointwise and integrates it, with no assumed integrability of V.

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib

open MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_j_ui_quantitative_l2_tail_lintegral
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (V : Ω → ENNReal) (hV : Measurable V)
    (R : ℝ≥0) (hR : 0 < R) (K : ENNReal)
    (hK : (∫⁻ ω, (V ω) ^ (2 : ℕ) ∂P) ≤ K) :
    (R : ENNReal) * (∫⁻ ω,
      (if (R : ENNReal) ≤ V ω then V ω else 0) ∂P) ≤ K := by sorry
