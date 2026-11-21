-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_original_past_coefficient_future_fullmark_condExp_zero_cross
-- name    : AvramDividend.Classical.avram_pj_original_past_coefficient_future_fullmark_condExp_zero_cross
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T10:00:43.62592+00:00
-- url     : https://prove2.me/theorems/9967dcc3-3781-407f-9585-046a932a1d51
-- title:
--   Zero true-filtration future compensated Lévy mark conditional expectation forces past predictable weighted cross moment zero
-- statement:
--   A strongly measurable past predictable coefficient U and an integrable future negative Levy marked count increment V have zero expected cross product whenever the original filtration conditional expectation of V is zero. This is a generic exact probability-space conditional expectation pull-out and is applicable with the already Proved original complete negative cutoff count conditional L2 theorem, under genuine integrability of the product.

import Mathlib
open MeasureTheory Set Filter Topology
noncomputable section

theorem AvramDividend.Classical.avram_pj_original_past_coefficient_future_fullmark_condExp_zero_cross
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (U V : Ω → ℝ)
    (hU : StronglyMeasurable[m] U)
    (hUI : Integrable (fun ω => U ω * V ω) P)
    (hVI : Integrable V P)
    (hVcentred : P[V | m] =ᵐ[P] (fun _ => (0 : ℝ))) :
    (∫ ω, U ω * V ω ∂P) = 0 := by sorry
