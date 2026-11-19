-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_reward65_fixed_double_integral_strongly_measurable
-- name    : AvramDividend.Classical.avram_pj_reward65_fixed_double_integral_strongly_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T19:15:28.492816+00:00
-- url     : https://prove2.me/theorems/bb50d8ef-adf0-4dab-b675-8bcfddff0f9c
-- title:
--   Jointly strongly measurable signed kernel has measurable fixed iterated Bochner integral
-- statement:
--   For arbitrary measurable sample ω, source time α and mark β, under s-finite fixed time and mark measures, a strongly measurable physical kernel in (z,(t,ω)) yields a strongly measurable real-valued random iterated integral ω↦∫t ∫z F(ω,t,z). Mathlib strong measurability of both fixed-kernel integrals. A reusable analytic transfer toward the original Levy predictable-clock measurability source53, with no stochastic centring assumption.
-- source:
--   Pinned Mathlib MeasureTheory.StronglyMeasurable.integral_prod_left' composed twice.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_pj_reward65_fixed_double_integral_strongly_measurable
    {Ω α β : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β)
    [SFinite μ] [SFinite ν]
    (F : Ω → α → β → ℝ)
    (hF : StronglyMeasurable (fun p : β × (α × Ω) =>
      F p.2.2 p.2.1 p.1)) :
    StronglyMeasurable (fun ω : Ω =>
      ∫ t, ∫ z, F ω t z ∂ν ∂μ) := by sorry
