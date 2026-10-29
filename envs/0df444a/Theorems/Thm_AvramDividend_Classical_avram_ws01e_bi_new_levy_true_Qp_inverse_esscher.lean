-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_bi_new_levy_true_Qp_inverse_esscher
-- name    : AvramDividend.Classical.avram_ws01e_bi_new_levy_true_Qp_inverse_esscher
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T00:27:50.865532+00:00
-- url     : https://prove2.me/theorems/f5f027eb-712c-497c-b646-c0f930391848
-- title:
--   Exact genuine tilted random-terminal Esscher-to-original exponential-clock inverse change of measure
-- statement:
--   For an actual spectrally negative Lévy process X, positive Exp(p) real observation clock, any Esscher parameter φ with ψ(φ)=q≥0, and arbitrary jointly measurable nonnegative extended-real terminal reward W, multiplication by exp(-φ X_e) under the genuine random-terminal withDensity Qp transforms the expectation into p/(p+q) times the original P×Exp(p+q) reward integral. This holds with all real-clock toNNReal casts and exact density, no global product tilted path/clock law and no infinite integrals divided.
-- source:
--   Canonically Proved joint time/state measurability d55462c3 and generic toNNReal clock-corrected inverse Esscher theorem avram_ws01e_bi_new_inverse_clock_cast_corrected (pending). Exact source root substitution ψφ=q. Needed by WS1A/WS1B original-clock killed-resolvent Wiener-Hopf transfer; do not publish before generic cast-corrected theorem is canonically Proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bi_new_inverse_clock_cast_corrected

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_bi_new_levy_true_Qp_inverse_esscher
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (φ q p : ℝ) (hq : 0 ≤ q)
    (hroot : X.ψ φ = q) (hp : 0 < p)
    (W : Ω × ℝ → ℝ≥0∞) (hW : Measurable W) :
    ENNReal.ofReal (p + q) *
      (∫⁻ z : Ω × ℝ,
        ENNReal.ofReal (Real.exp (-φ * X.X (Real.toNNReal z.2) z.1)) * W z
        ∂((P.prod (expMeasure p)).withDensity
          (fun z : Ω × ℝ => ENNReal.ofReal
            (Real.exp (φ * X.X (Real.toNNReal z.2) z.1 -
              (Real.toNNReal z.2 : ℝ) * X.ψ φ))))) =
    ENNReal.ofReal p *
      (∫⁻ z : Ω × ℝ, W z ∂(P.prod (expMeasure (p + q)))) := by sorry
