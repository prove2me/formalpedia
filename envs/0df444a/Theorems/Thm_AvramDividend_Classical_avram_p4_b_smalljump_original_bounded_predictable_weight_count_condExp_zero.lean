-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_bounded_predictable_weight_count_condExp_zero
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_bounded_predictable_weight_count_condExp_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:27:43.274815+00:00
-- url     : https://prove2.me/theorems/c587c43a-5c4f-47d8-81e7-a8ed487bd322
-- title:
--   Original Lévy bounded random predictable coefficient preserves centred count conditional expectation
-- statement:
--   For the exact original Lévy intrinsic marked jump count, its centred finite-band real increment having zero conditional expectation remains conditionally centred after multiplication by a genuinely random bounded coefficient measurable in the same original right-continuous past. The source count, clock and probability space are unchanged; finite-band first-moment conditional centring is supplied explicitly.
-- source:
--   Mathlib condExp_stronglyMeasurable_mul_of_bound on the original filtration (Filtration.le).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_bounded_predictable_weight_count_condExp_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (B : Set ℝ) (J : Ω → ℝ≥0∞)
    (hJsource : ∀ ω, J ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
       (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
       (Ioc s t ×ˢ B))
    (rate : ℝ≥0∞)
    (hYint : Integrable (fun ω => (J ω).toReal - rate.toReal) P)
    (hYcenter :
      P[(fun ω => (J ω).toReal - rate.toReal) | 𝓕.rightCont s] =ᵐ[P] 0)
    (H : Ω → ℝ) (C : ℝ)
    (hH : StronglyMeasurable[𝓕.rightCont s] H)
    (hBound : ∀ᵐ ω ∂P, ‖H ω‖ ≤ C) :
    P[(fun ω => H ω * ((J ω).toReal - rate.toReal)) |
      𝓕.rightCont s] =ᵐ[P] 0 := by sorry
