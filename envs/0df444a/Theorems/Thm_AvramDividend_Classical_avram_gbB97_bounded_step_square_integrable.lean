-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB97_bounded_step_square_integrable
-- name    : AvramDividend.Classical.avram_gbB97_bounded_step_square_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T22:00:35.49091+00:00
-- url     : https://prove2.me/theorems/e2c5e8a3-8b09-4db9-95da-352868888e26
-- title:
--   Finite-measure integrability of squared differences of original bounded grid coefficients
-- statement:
--   The original two-grid stopped Gaussian coefficients are strongly measurable and uniformly bounded. On the original finite probability measure, each squared difference of two such coefficients has finite integral. This supplies the exact integrability premise for B85's finite-step time expectation identity in B82.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB97_bounded_step_square_integrable
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (G : ℕ → ℕ → Ω → ℝ)
    (hG : ∀ a i, StronglyMeasurable (G a i))
    (B : ℝ) (hB : 0 ≤ B)
    (hBound : ∀ a i ω, |G a i ω| ≤ B)
    (m p r : ℕ) :
    Integrable (fun ω => (G m (r / (p + 1)) ω -
      G p (r / (m + 1)) ω) ^ 2) P := by sorry
