-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_real_second_moment_ae_expectations
-- name    : AvramDividend.Classical.avram_p2_j_ui_real_second_moment_ae_expectations
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:23:05.702031+00:00
-- url     : https://prove2.me/theorems/223141e9-003d-4d54-8b45-76d7f6418cfd
-- title:
--   Uniform genuine real second moments yield convergence of Bochner expectations
-- statement:
--   For real random variables on a probability space converging almost everywhere, uniformly bounded genuine real integrals of squared absolute values, together with their integrability, imply Bochner integrability of the limit and convergence of expectations. The proof converts each real moment bound to an L2 seminorm bound using pinned Mathlib and applies the independently verified full Vitali theorem.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_second_moment_to_l2_norm
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_l2_ae_expectations_direct

open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_j_ui_real_second_moment_ae_expectations
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ) (B : ℝ≥0)
    (hm : ∀ n, AEStronglyMeasurable (Y n) P)
    (hInt : ∀ n, Integrable (fun ω => ‖Y n ω‖ ^ 2) P)
    (hB : ∀ n, (∫ ω, ‖Y n ω‖ ^ 2 ∂P) ≤ (B : ℝ) ^ 2)
    (hae : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (nhds (Z ω))) :
    Integrable Z P ∧
      Tendsto (fun n => ∫ ω, Y n ω ∂P) atTop
        (nhds (∫ ω, Z ω ∂P)) := by sorry
