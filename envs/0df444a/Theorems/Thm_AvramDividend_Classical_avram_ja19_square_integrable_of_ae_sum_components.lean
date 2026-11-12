-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja19_square_integrable_of_ae_sum_components
-- name    : AvramDividend.Classical.avram_ja19_square_integrable_of_ae_sum_components
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T12:04:38.009454+00:00
-- url     : https://prove2.me/theorems/d3782c63-39ff-4c8f-a536-03cbc5f0b73e
-- title:
--   A measurable sum has integrable square when each component has an integrable square
-- statement:
--   Generic analytic L2 domination. The summands need only have measurable squares, while the observed sum is assumed almost-everywhere strongly measurable. The latter follows from original-filtration adaptedness of the actual Gaussian residual.
-- source:
--   J-A19 finite-activity same-triplet bridge and original filtration residual adaptedness

import Mathlib
open MeasureTheory
noncomputable section

theorem AvramDividend.Classical.avram_ja19_square_integrable_of_ae_sum_components
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f G J : α → ℝ)
    (hf : AEStronglyMeasurable f μ)
    (hG : Integrable (fun ω => (G ω) ^ 2) μ)
    (hJ : Integrable (fun ω => (J ω) ^ 2) μ)
    (heq : ∀ᵐ ω ∂μ, f ω = G ω + J ω) :
    Integrable (fun ω => (f ω) ^ 2) μ := by sorry
