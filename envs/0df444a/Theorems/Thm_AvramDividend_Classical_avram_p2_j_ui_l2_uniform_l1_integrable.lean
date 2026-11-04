-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_l2_uniform_l1_integrable
-- name    : AvramDividend.Classical.avram_p2_j_ui_l2_uniform_l1_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T17:19:16.661977+00:00
-- url     : https://prove2.me/theorems/cdf3f35d-69ec-4d28-abfe-fa5e2e077c50
-- title:
--   Uniform L² seminorm bound yields integrable real variables and uniform L¹ bound
-- statement:
--   For a sequence of almost-everywhere strongly measurable real random variables on a probability space, a single finite bound on all L2 seminorms ensures that every variable is genuinely Bochner-integrable and that all L1 seminorms obey the same bound. This converts source moment estimates to integrability data without invoking jump compensation, pathwise convergence or any model-specific law.

import Mathlib

open MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_j_ui_l2_uniform_l1_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (B : ℝ≥0)
    (hm : ∀ n, AEStronglyMeasurable (Y n) P)
    (hB : ∀ n, eLpNorm (Y n) 2 P ≤ (B : ENNReal)) :
    ∀ n, Integrable (Y n) P ∧
      eLpNorm (Y n) 1 P ≤ (B : ENNReal) := by sorry
