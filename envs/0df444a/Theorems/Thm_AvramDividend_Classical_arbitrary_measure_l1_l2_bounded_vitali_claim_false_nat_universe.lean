-- Prove2me | Theorems.Thm_AvramDividend_Classical_arbitrary_measure_l1_l2_bounded_vitali_claim_false_nat_universe
-- name    : AvramDividend.Classical.arbitrary_measure_l1_l2_bounded_vitali_claim_false_nat_universe
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T10:56:54.040743+00:00
-- url     : https://prove2.me/theorems/5595dc77-05c4-428f-a233-d01bcf8a0fee
-- title:
--   Formal universe-zero negation of arbitrary-measure bounded L1/L2 Vitali mean convergence
-- statement:
--   Bounded L1 and L2 norms plus almost-everywhere convergence are insufficient to force Bochner expectation convergence on unrestricted infinite measure spaces. A moving singleton on natural counting measure has both norms one and a.e. pointwise zero limit while its expectation is always one. The kernel-verifiable theorem negates the full universally quantified but universe-zero claim, and identifies precisely the missing finite-measure or tightness assumption.
-- source:
--   Negation certificate for retired invalid Avram theorem 685bb004, using accepted Proved counting_delta_l2_bounded_ae_but_not_mean_convergent (2db878b8)

import Mathlib
import Theorems.Thm_AvramDividend_Classical_counting_delta_l2_bounded_ae_but_not_mean_convergent
open MeasureTheory Filter Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.arbitrary_measure_l1_l2_bounded_vitali_claim_false_nat_universe :
    ¬ (∀ {Ω : Type} [MeasurableSpace Ω]
      (μ : Measure Ω) (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ)
      (B D : ℝ≥0),
      (∀ n, AEStronglyMeasurable (Y n) μ) →
      (∀ n, eLpNorm (Y n) 2 μ ≤ (B : ENNReal)) →
      (∀ n, eLpNorm (Y n) 1 μ ≤ (D : ENNReal)) →
      (∀ᵐ ω ∂μ, Tendsto (fun n => Y n ω) atTop (nhds (Z ω))) →
      Integrable Z μ ∧
        Tendsto (fun n => ∫ ω, Y n ω ∂μ) atTop
          (nhds (∫ ω, Z ω ∂μ))) := by sorry
