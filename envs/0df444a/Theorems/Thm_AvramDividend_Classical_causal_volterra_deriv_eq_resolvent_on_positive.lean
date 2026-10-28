-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_volterra_deriv_eq_resolvent_on_positive
-- name    : AvramDividend.Classical.causal_volterra_deriv_eq_resolvent_on_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T10:56:35.137444+00:00
-- url     : https://prove2.me/theorems/dabc7a99-0459-4809-ab8a-fe2fb0d64436
-- title:
--   Derivative of the Volterra scale solution equals its continuous resolvent
-- statement:
--   Given a locally bounded continuous solution V of the integrated Gaussian Esscher second-kind Volterra equation and a continuous derivative resolvent g solving its corresponding constant-forcing equation, uniqueness identifies V with the positive-time integral primitive of g. Hence deriv V x = g x for every x>0. This is the exact derivative identity needed to transport the Gaussian origin slope through Esscher untilting.
-- source:
--   Previously Proved causal_volterra_C2_of_C1_derivative_resolvent proof, with unnecessary C1 regularity of g removed and its derivative identity extracted.

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_causal_primitive_C1_locally_bounded
import Theorems.Thm_AvramDividend_Classical_causal_volterra_integrated_identity_of_resolvent
import Theorems.Thm_AvramDividend_Classical_causal_volterra_l1_continuous_solution_unique
import Theorems.Thm_AvramDividend_Classical_causal_primitive_deriv_eq_continuous_on_positive
open AvramDividend.Classical MeasureTheory Set Filter

namespace AvramDividend.Classical
/-- A positive-time Volterra solution has derivative equal to its continuous resolvent. -/
theorem causal_volterra_deriv_eq_resolvent_on_positive
    (K g V : ℝ → ℝ) (a β : ℝ) (ha : 0 < a)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hVc : ContinuousOn V (Ioi (0 : ℝ)))
    (hVb : ∀ R : ℝ, 0 < R →
      ∃ C : ℝ, ∀ x : ℝ, x ∈ Ioc (0 : ℝ) R → |V x| ≤ C)
    (hVe : ∀ x : ℝ, 0 < x →
      a * V x +
        (∫ s in Ioc (0 : ℝ) x,
          (β + K (x - s)) * V s ∂volume) = x)
    (hg : ContinuousOn g (Ici (0 : ℝ)))
    (hgeq : ∀ x : ℝ, 0 < x →
      a * g x +
        (∫ s in Ioc (0 : ℝ) x,
          (β + K (x - s)) * g s ∂volume) = 1) :
    ∀ x : ℝ, 0 < x → deriv V x = g x := by
  sorry
end AvramDividend.Classical
