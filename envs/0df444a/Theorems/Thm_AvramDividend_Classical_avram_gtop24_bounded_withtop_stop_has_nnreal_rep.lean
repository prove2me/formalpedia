-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gtop24_bounded_withtop_stop_has_nnreal_rep
-- name    : AvramDividend.Classical.avram_gtop24_bounded_withtop_stop_has_nnreal_rep
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T02:55:20.013916+00:00
-- url     : https://prove2.me/theorems/29bde75d-07e5-4b1f-b334-797b5630a9e7
-- title:
--   A bounded WithTop stopping clock has an exact finite NNReal stopping-time representative
-- statement:
--   Necessary original-filtration coercion bridge for the lower sampled exit family and its supremum in Open f9caff29. Pointwise bounded WithTop clocks are finite, so their exact NNReal representatives retain stopping-time measurability and the original bound.
-- source:
--   Exact root-connected Gaussian lower-clock normalization; no probabilistic hypotheses or auxiliary processes.

import Mathlib
import Mathlib.Probability.Process.Stopping
open MeasureTheory Set
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_gtop24_bounded_withtop_stop_has_nnreal_rep
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (σ : Ω → ℝ≥0)
    (R : Ω → WithTop ℝ≥0)
    (hRstop : IsStoppingTime 𝓕.rightCont R)
    (hRle : ∀ ω, R ω ≤ (σ ω : WithTop ℝ≥0)) :
    ∃ L : Ω → ℝ≥0,
      (∀ ω, (L ω : WithTop ℝ≥0) = R ω) ∧
      IsStoppingTime 𝓕.rightCont (fun ω => (L ω : WithTop ℝ≥0)) ∧
      ∀ ω, L ω ≤ σ ω := by sorry
