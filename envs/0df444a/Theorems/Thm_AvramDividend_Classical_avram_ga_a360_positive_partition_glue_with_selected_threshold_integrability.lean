-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a360_positive_partition_glue_with_selected_threshold_integrability
-- name    : AvramDividend.Classical.avram_ga_a360_positive_partition_glue_with_selected_threshold_integrability
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T12:02:22.801406+00:00
-- url     : https://prove2.me/theorems/73a09e6a-7901-4585-9975-0f66e438dcf0
-- title:
--   Positive full-cell partition has integrable vanishing expectation when each tolerance selects one integrable small threshold
-- statement:
--   For a positive full source split into small and large threshold parts, assume full positive source a.e. strongly measurable, large positive source integrable with vanishing expected contribution for every positive threshold, and for every tolerance an eventually small expected small-source budget together with integrability at the selected threshold. The entire full positive source is integrable at every mesh and its expected value converges to zero. The theorem avoids the stronger unnecessary requirement that the small part is integrable for every arbitrarily large threshold, a blocker in the original Gaussian small increment a264 route.
-- source:
--   Original full Gaussian a216 pointwise small/large partition a266, full aestrongly measurable a267, large expected L1 a263; reduces the remaining source to selected-threshold small-cell budget.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ga_a280_positive_fullcell_integrable_of_measurable_masked_partition
open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a360_positive_partition_glue_with_selected_threshold_integrability
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F : ℕ → Ω → ℝ) (S L : ℝ → ℕ → Ω → ℝ)
    (hFm : ∀ m, AEStronglyMeasurable (fun ω => max (F m ω) 0) P)
    (hLI : ∀ δ, 0 < δ → ∀ m,
      Integrable (fun ω => max (L δ m ω) 0) P)
    (hPt : ∀ δ, 0 < δ → ∀ m ω,
      max (F m ω) 0 ≤ max (S δ m ω) 0 + max (L δ m ω) 0)
    (hL : ∀ δ, 0 < δ →
      Tendsto (fun m => ∫ ω, max (L δ m ω) 0 ∂P)
        atTop (𝓝 (0 : ℝ)))
    (hS : ∀ η, 0 < η →
      ∃ δ, 0 < δ ∧
        (∀ m, Integrable (fun ω => max (S δ m ω) 0) P) ∧
        ∃ k : ℕ, ∀ m, k ≤ m →
          (∫ ω, max (S δ m ω) 0 ∂P) ≤ η) :
    (∀ m, Integrable (fun ω => max (F m ω) 0) P) ∧
      Tendsto (fun m => ∫ ω, max (F m ω) 0 ∂P)
        atTop (𝓝 (0 : ℝ)) := by sorry
