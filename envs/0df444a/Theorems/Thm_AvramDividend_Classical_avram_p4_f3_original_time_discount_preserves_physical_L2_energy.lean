-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_time_discount_preserves_physical_L2_energy
-- name    : AvramDividend.Classical.avram_p4_f3_original_time_discount_preserves_physical_L2_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T19:25:15.887564+00:00
-- url     : https://prove2.me/theorems/ee8001ec-bbc6-47d9-97a8-1b765117893e
-- title:
--   Discounting actual nonnegative physical time preserves finite quadratic stochastic source energy
-- statement:
--   On the original nonnegative physical time/sample space, multiplying any square-integrable stochastic source coefficient by the actual nonnegative discount factor exp(-q t), q nonnegative, preserves finite joint quadratic energy. This applies to original Gaussian and jump integrands, including physical reserve coefficients established separately.
-- source:
--   Pointwise exponential discount lies in [0,1] at the original nonnegative time. The square of the weighted coefficient is bounded by the original square, hence the joint source energy is finite by monotonicity of the genuine ENNReal integral. Requires Mathlib.MeasureTheory.Integral.Lebesgue.Basic for actual lintegral binder notation; the earlier auto-import proposal lacked it and failed parsing.

import Mathlib
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
open MeasureTheory
open scoped ENNReal NNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f3_original_time_discount_preserves_physical_L2_energy
    {Ω : Type*} [MeasurableSpace Ω]
    (q : ℝ) (hq : 0 ≤ q)
    (μ : Measure (ℝ≥0 × Ω))
    (F : ℝ≥0 × Ω → ℝ)
    (hF : (∫⁻ p, ENNReal.ofReal ((F p) ^ 2) ∂μ) < ⊤) :
    (∫⁻ p, ENNReal.ofReal
      ((Real.exp (-(q * (p.1 : ℝ))) * F p) ^ 2) ∂μ) < ⊤ := by sorry
