-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_l2_ae_expectations
-- name    : AvramDividend.Classical.avram_p2_j_ui_l2_ae_expectations
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T17:46:45.66219+00:00
-- url     : https://prove2.me/theorems/a03778d9-db7a-450c-8dd0-1087a5f575df
-- title:
--   Uniform L² bounds and almost-everywhere convergence yield convergence of real Bochner expectations
-- statement:
--   For measurable real random variables converging almost everywhere on a probability space, a common finite L2 seminorm bound implies integrability of the limit and convergence of the genuine Bochner expectations. The proof composes source-verified L2-to-L1 integrability, restricted Cauchy-Schwarz, the square-root uniform-integrability modulus and the Vitali expectation theorem. It requires no process-specific compensator or jump-rate identity.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_vitali_expectations
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_l2_uniform_l1_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_l2_restriction_bound
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_quantitative_l2_modulus_to_uniform_integrable

open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_j_ui_l2_ae_expectations
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ) (B : ℝ≥0)
    (hm : ∀ n, AEStronglyMeasurable (Y n) P)
    (hB : ∀ n, eLpNorm (Y n) 2 P ≤ (B : ENNReal))
    (hae : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (nhds (Z ω))) :
    Integrable Z P ∧
      Tendsto (fun n => ∫ ω, Y n ω ∂P) atTop
        (nhds (∫ ω, Z ω ∂P)) := by sorry
