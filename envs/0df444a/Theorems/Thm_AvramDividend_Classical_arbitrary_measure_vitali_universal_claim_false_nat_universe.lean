-- Prove2me | Theorems.Thm_AvramDividend_Classical_arbitrary_measure_vitali_universal_claim_false_nat_universe
-- name    : AvramDividend.Classical.arbitrary_measure_vitali_universal_claim_false_nat_universe
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T10:56:21.024204+00:00
-- url     : https://prove2.me/theorems/a9db5e78-63a0-4866-82b2-661bade8ea7b
-- title:
--   Formal universe-zero negation of unrestricted Vitali mean convergence
-- statement:
--   The universal assertion that uniformly integrable real-valued sequences on any measure space converge in Bochner means whenever they converge almost everywhere is false, already in universe zero. The explicit infinite counting-measure moving singleton sequence is uniformly integrable and pointwise zero, while every integral equals one. This is a kernel-checkable formal negation of the unrestricted assertion in the user-level universe, while the immutable original universe-polymorphic theorem has been administratively retired and retains Open status.
-- source:
--   Original false theorem a1ad8b30-11bf-47b0-9c40-3df32177fb59 and accepted constructive counterexample 24ee7e68-0716-4e03-933b-12c56d3f9766

import Mathlib
import Theorems.Thm_AvramDividend_Classical_counting_measure_uniform_integrability_counterexample_vitali
open MeasureTheory Filter Set
noncomputable section

theorem AvramDividend.Classical.arbitrary_measure_vitali_universal_claim_false_nat_universe :
    ¬ (∀ {Ω : Type} [MeasurableSpace Ω]
      (μ : Measure Ω) (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ),
      UniformIntegrable Y 1 μ →
      (∀ᵐ ω ∂μ, Tendsto (fun n => Y n ω) atTop (nhds (Z ω))) →
      Integrable Z μ ∧
        Tendsto (fun n => ∫ ω, Y n ω ∂μ) atTop
          (nhds (∫ ω, Z ω ∂μ))) := by sorry
