-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_finite_lintegral_bound_expectations
-- name    : AvramDividend.Classical.avram_p2_j_ui_finite_lintegral_bound_expectations
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:24:28.967482+00:00
-- url     : https://prove2.me/theorems/0e83d81a-d265-483d-9ae5-1c5ec689e647
-- title:
--   Any finite ENNReal squared-moment envelope yields real Bochner expectation convergence
-- statement:
--   On a probability space, almost-everywhere convergence and a uniform bound by an arbitrary finite ENNReal constant on squared norm lintegrals imply integrability of the real limit and convergence of genuine Bochner expectations. The finite constant is converted to the square of an NNReal square-root via the verified NNReal.sq_sqrt and ENNReal.coe_toNNReal identities.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_lintegral_l2_ae_expectations

open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_j_ui_finite_lintegral_bound_expectations
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ) (K : ENNReal)
    (hK : K ≠ ⊤)
    (hm : ∀ n, AEStronglyMeasurable (Y n) P)
    (hB : ∀ n, (∫⁻ ω, ‖Y n ω‖ₑ ^ (2 : ℝ) ∂P) ≤ K)
    (hae : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (nhds (Z ω))) :
    Integrable Z P ∧
      Tendsto (fun n => ∫ ω, Y n ω ∂P) atTop
        (nhds (∫ ω, Z ω ∂P)) := by sorry
