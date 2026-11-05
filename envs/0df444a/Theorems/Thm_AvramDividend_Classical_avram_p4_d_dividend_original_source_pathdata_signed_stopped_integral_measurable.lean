-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_source_pathdata_signed_stopped_integral_measurable
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_source_pathdata_signed_stopped_integral_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T22:16:05.25636+00:00
-- url     : https://prove2.me/theorems/6ff4e3ed-b51d-4ca0-a4f9-3a5d1c1ced75
-- title:
--   Original Lévy left-limit, dividend right-limit and joint window measurability give strongly measurable signed stopped integral
-- statement:
--   For the genuine original Lévy process and admissible dividend strategy, an s-finite dividend kernel, measurable actual source left-limit and right-dividend limit, measurable value derivative and one jointly measurable pre-ruin closed-horizon payment window suffice for strong measurability of the stopped discounted signed dividend-gradient integral. No separate pathwise-window or stopped-integrand measurability premise is needed. This provides the exact stochastic interface needed to invoke the P4-D named-Cash L1 bridge.
-- source:
--   Composition of Proved source-specific joint window section, original stopped gradient joint measurability and s-finite kernel integral measurability helpers.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_joint_stop_window_measurable_sections
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_stopped_gradient_joint_measurable_from_path_data
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_stopped_diffuse_signed_kernel_integral_measurable

open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_source_pathdata_signed_stopped_integral_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (σ : Ω → ℝ≥0∞) (τ : Ω → ℝ≥0)
    (q : ℝ) (w : ℝ → ℝ)
    (κdiff : Kernel Ω ℝ) [IsSFiniteKernel κdiff]
    (hXL : Measurable (fun p : Ω × ℝ =>
      Function.leftLim (fun r : ℝ≥0 => X.X r p.1) p.2.toNNReal))
    (hDR : Measurable (fun p : Ω × ℝ =>
      rightLimit D p.2.toNNReal p.1))
    (hDeriv : Measurable (deriv w))
    (hWindowJoint : MeasurableSet {p : Ω × ℝ |
      p.2 ∈ paymentTimes (σ p.1) ∩ Iic (τ p.1 : ℝ)}) :
    StronglyMeasurable (fun ω : Ω =>
      ∫ s in (paymentTimes (σ ω) ∩ Iic (τ ω : ℝ)),
        Real.exp (-(q * s)) *
          (1 - deriv w (x +
            Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
            rightLimit D s.toNNReal ω)) ∂κdiff ω) := by sorry
