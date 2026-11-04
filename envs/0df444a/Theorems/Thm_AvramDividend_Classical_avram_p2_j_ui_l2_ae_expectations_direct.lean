-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_l2_ae_expectations_direct
-- name    : AvramDividend.Classical.avram_p2_j_ui_l2_ae_expectations_direct
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T17:26:16.952767+00:00
-- url     : https://prove2.me/theorems/c230d3a7-424e-4e1d-b366-03fab9010fa6
-- title:
--   Self-contained real Bochner Vitali theorem from a uniform L² bound
-- statement:
--   Given a common finite L2 seminorm bound for measurable real random variables on a probability space and pointwise a.e. convergence, derive L1 uniform integrability by restricted Hölder and a square-root modulus, show the limit is integrable, and prove convergence of genuine Bochner expectations. Independent of model-specific jump results and of any newly published helper theorem.

import Mathlib

open MeasureTheory Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_j_ui_l2_ae_expectations_direct
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ) (B : ℝ≥0)
    (hm : ∀ n, AEStronglyMeasurable (Y n) P)
    (hB : ∀ n, eLpNorm (Y n) 2 P ≤ (B : ENNReal))
    (hae : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (nhds (Z ω))) :
    Integrable Z P ∧
      Tendsto (fun n => ∫ ω, Y n ω ∂P) atTop
        (nhds (∫ ω, Z ω ∂P)) := by sorry
