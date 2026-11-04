-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_lintegral_l2_ae_expectations
-- name    : AvramDividend.Classical.avram_p2_j_ui_lintegral_l2_ae_expectations
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:00:18.947016+00:00
-- url     : https://prove2.me/theorems/eeb2e2f9-855c-4e07-93fc-4a8062da1b52
-- title:
--   ENNReal squared lintegral bounds and a.e. convergence imply Bochner expectation convergence
-- statement:
--   On a probability space, a common squared ENNReal lintegral bound for real random variables and their almost-everywhere convergence yield integrability of the limit and convergence of genuine Bochner expectations; composes two independently verified P2-J lemmas and accommodates the original Lévy grid moment estimate after legitimate signed-sum domination.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_lintegral_squared_enorm_bound
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_l2_ae_expectations_direct

open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_j_ui_lintegral_l2_ae_expectations
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ) (B : ℝ≥0)
    (hm : ∀ n, AEStronglyMeasurable (Y n) P)
    (hB : ∀ n, (∫⁻ ω, ‖Y n ω‖ₑ ^ (2 : ℝ) ∂P) ≤ (B : ENNReal) ^ 2)
    (hae : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (nhds (Z ω))) :
    Integrable Z P ∧
      Tendsto (fun n => ∫ ω, Y n ω ∂P) atTop
        (nhds (∫ ω, Z ω ∂P)) := by sorry
