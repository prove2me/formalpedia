-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_chat24_bounded_ae_limit_integrable
-- name    : AvramDividend.Classical.avram_chat24_bounded_ae_limit_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T21:34:25.007183+00:00
-- url     : https://prove2.me/theorems/e43715dc-064f-4af6-a49a-4ffb7187c0ab
-- title:
--   A uniformly bounded AE limit is integrable on a finite measure space
-- statement:
--   On any finite measure space, an AE pointwise limit of measurable real functions with one uniform norm bound is integrable. AE strong measurability passes to the limit, the norm bound passes by continuity of the norm, and integrability follows by comparison with the constant. This is the final integrability step of parent 7b52eba8-6fe9-40c9-89f7-a341ca70210b. Pinned remote signature evidence confirms the atTop argument of aestronglyMeasurable_of_tendsto_ae; applicability remains to be compiled.

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_chat24_bounded_ae_limit_integrable
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (F : ℕ → α → ℝ) (g : α → ℝ) (C : ℝ)
    (hF : ∀ n, AEStronglyMeasurable (F n) μ)
    (hbound : ∀ n t, ‖F n t‖ ≤ C)
    (hlim : ∀ᵐ t ∂μ, Tendsto (fun n => F n t) atTop (nhds (g t))) :
    Integrable g μ := by sorry
