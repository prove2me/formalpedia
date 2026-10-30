-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01h_actual_Qp_full_survival_finite_clock_uncapping_error
-- name    : AvramDividend.Classical.avram_ws01h_actual_Qp_full_survival_finite_clock_uncapping_error
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T11:49:44.772247+00:00
-- url     : https://prove2.me/theorems/d84e7090-bafd-41a8-8d92-5f2ec168419e
-- title:
--   Actual Esscher Qp finite-clock lower-survival truncation error bounded by exact exp(-pN) tail
-- statement:
--   For the genuine terminal Esscher tilt Qp of an original Lévy path and real Exp(p) observation clock, full lower nonruin survival at initial reserve x is squeezed between the same event capped to observed time≤N and that capped mass plus exp(-pN). This is source specific and holds at x=0 and every finite nonnegative N. It follows from a measurable event-cover by the cap and real-clock tail, combined with the exact source-specific Qp observation-clock marginal, and supplies the quantitative uncapping step in finite-rate killed Esscher CDF renewal.
-- source:
--   Proved true Qp exponential tail exact theorem WS01H, source original full-history reserve event, and Mathlib measure_mono/measure_union_le.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_actual_Qp_exp_clock_finite_cap_tail_exact

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01h_actual_Qp_full_survival_finite_clock_uncapping_error
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p)
    (x : ℝ) (N : ℝ≥0) :
    (let Qp : Measure (Ω × ℝ) :=
       (P.prod (expMeasure p)).withDensity
         (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
           (θ * X.X (Real.toNNReal z.2) z.1 -
             (Real.toNNReal z.2 : ℝ) * X.ψ θ)))
     let E : Set (Ω × ℝ) := {z | 0 ≤ z.2 ∧
       ∀ s : ℝ≥0, s ≤ Real.toNNReal z.2 → -x ≤ X.X s z.1}
     let C : Set (Ω × ℝ) := {z | 0 ≤ z.2 ∧
       Real.toNNReal z.2 ≤ N ∧
       ∀ s : ℝ≥0, s ≤ Real.toNNReal z.2 → -x ≤ X.X s z.1}
     Qp C ≤ Qp E ∧
       Qp E ≤ Qp C + ENNReal.ofReal (Real.exp (-(p * (N : ℝ))))) := by sorry
