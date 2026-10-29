-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_bi_new_inverse_clock_cast_corrected
-- name    : AvramDividend.Classical.avram_ws01e_bi_new_inverse_clock_cast_corrected
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T00:19:24.767535+00:00
-- url     : https://prove2.me/theorems/ce964d23-179c-4769-b9d2-d9f1de8ab04b
-- title:
--   Actual nonnegative-clock cast-corrected inverse Esscher rate-shift identity
-- statement:
--   For p>0, q≥0, any real α and jointly measurable real F and nonnegative extended-real reward W, inverse Esscher weighting under the genuinely nonnegative-real-clock density exp(αF-q*Real.toNNReal(e)) transforms the joint path/Exp(p) measure into the original path/Exp(p+q) reward integral, with exact ratio p/(p+q). The equality is valid as ENNReal without finiteness assumptions and does not presume the density defines an independent tilted product law.
-- source:
--   Accepted strict Exp(p) clock tail theorem 69bfdea1 gives probability one on e>0; pinned MeasureTheory.measure_compl, Measure.ae_prod_iff_ae_ae, withDensity_congr_ae identify the toNNReal and real-clock densities; then accepted generic inverse Esscher clock theorem 46fb20aa proves the identity. The latter must become canonically Proved before publication.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_expMeasure_strict_survival_real
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bi_new_inverse_clock_esscher_weight

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.avram_ws01e_bi_new_inverse_clock_cast_corrected
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
            ENNReal.ofReal (Real.exp
              (α * F z - (Real.toNNReal z.2 : ℝ) * q))))) =
    ENNReal.ofReal p *
      (∫⁻ z : Ω × ℝ, W z ∂(P.prod (expMeasure (p + q)))) := by sorry
