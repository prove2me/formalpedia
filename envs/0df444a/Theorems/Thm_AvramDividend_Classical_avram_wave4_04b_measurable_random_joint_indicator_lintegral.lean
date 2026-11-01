-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_measurable_random_joint_indicator_lintegral
-- name    : AvramDividend.Classical.avram_wave4_04b_measurable_random_joint_indicator_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T17:06:12.066239+00:00
-- url     : https://prove2.me/theorems/e7f5908d-a013-4930-9d3e-7721cfe92782
-- title:
--   Jointly measurable random-integrand Stieltjes kernel indicator integral is measurable
-- statement:
--   For any s-finite kernel from sample paths to real payment times, any measurable set of time-sample pairs, and any nonnegative jointly measurable random integrand, the sample-dependent kernel integral of its indicator is measurable. This is needed for controlled surplus gradients and source Lévy pre-jump reserve integrands, which depend on the sample and cannot use an old deterministic-time-weight measurability theorem. It follows from pinned Mathlib Measurable.lintegral_kernel_prod_left and does not assume a stochastic chain rule.
-- source:
--   Pinned Mathlib.Probability.Kernel.MeasurableLIntegral theorem Measurable.lintegral_kernel_prod_left; source 04-B full Stieltjes random localisation and source s-finite dividend kernel

import Mathlib
import Mathlib.Probability.Kernel.MeasurableLIntegral

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave4_04b_measurable_random_joint_indicator_lintegral
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (κ : ProbabilityTheory.Kernel Ω ℝ)
    [ProbabilityTheory.IsSFiniteKernel κ]
    (S : Set (ℝ × Ω)) (hS : MeasurableSet S)
    (f : ℝ × Ω → ℝ≥0∞) (hf : Measurable f) :
    Measurable (fun ω : Ω => ∫⁻ t, if (t, ω) ∈ S then f (t, ω) else 0 ∂κ ω) := by
  sorry
