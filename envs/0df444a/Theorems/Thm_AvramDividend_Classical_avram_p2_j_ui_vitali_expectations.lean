-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_vitali_expectations
-- name    : AvramDividend.Classical.avram_p2_j_ui_vitali_expectations
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T17:09:57.260181+00:00
-- url     : https://prove2.me/theorems/72ee70ab-5f4c-427c-8a2c-47b7b1cee385
-- title:
--   Almost-everywhere Vitali convergence implies convergence of real Bochner expectations
-- statement:
--   On a probability space, a uniformly integrable sequence of real functions converging almost everywhere to a limit has an integrable limit, and its genuine real Bochner expectations converge to the expectation of that limit. This theorem joins the pinned-Mathlib limit-integrability, L1-Vitali and Bochner-integral-continuity results and makes no assumption about Lévy processes or their jump compensators.

import Mathlib

open MeasureTheory Filter

theorem AvramDividend.Classical.avram_p2_j_ui_vitali_expectations
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ)
    (hUI : UniformIntegrable Y 1 P)
    (hae : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (nhds (Z ω))) :
    Integrable Z P ∧
      Tendsto (fun n => ∫ ω, Y n ω ∂P) atTop
        (nhds (∫ ω, Z ω ∂P)) := by sorry
