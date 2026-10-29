-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_bi_new_inverse_clock_esscher_weight
-- name    : AvramDividend.Classical.avram_ws01e_bi_new_inverse_clock_esscher_weight
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T00:12:27.405058+00:00
-- url     : https://prove2.me/theorems/46fb20aa-73cb-4fcb-8321-4381f3d0cc24
-- title:
--   Exact inverse Esscher-weight compensation by exponential clock rate shift
-- statement:
--   For any probability path law, positive exponential clock rate p, nonnegative rate shift q, any real tilt α, jointly measurable real terminal statistic F and nonnegative extended-real reward W, the inverse Esscher factor exp(-αF) under the joint withDensity proportional to exp(αF-q e) exactly yields the original P×Exp(p+q) reward integral after the factor (p+q)/p. Both sides are extended integrals, and no density normalisation is asserted for arbitrary F.
-- source:
--   Pointwise exp(αF-qe)*exp(-αF)=exp(-qe), accepted general joint product Exp rate shift fb763eda, and pinned lintegral_withDensity_eq_lintegral_mul. A source-faithful non-Levy interface for WS1A/WS1B original-clock Wiener–Hopf transfer; applying it to genuine X requires separate proof of real-clock vs toNNReal-clock density agreement on the supported exponential clock.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bi_new_joint_exp_clock_rate_shift

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.avram_ws01e_bi_new_inverse_clock_esscher_weight
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (p q α : ℝ) (hp : 0 < p) (hq : 0 ≤ q)
    (F : Ω × ℝ → ℝ) (hF : Measurable F)
    (W : Ω × ℝ → ℝ≥0∞) (hW : Measurable W) :
    ENNReal.ofReal (p + q) *
      (∫⁻ z : Ω × ℝ,
        ENNReal.ofReal (Real.exp (-α * F z)) * W z
        ∂((P.prod (expMeasure p)).withDensity
          (fun z : Ω × ℝ =>
            ENNReal.ofReal (Real.exp (α * F z - q * z.2))))) =
    ENNReal.ofReal p *
      (∫⁻ z : Ω × ℝ, W z ∂(P.prod (expMeasure (p + q)))) := by sorry
