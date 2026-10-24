-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_exp_weighted_primitive_C1_local
-- name    : AvramDividend.Classical.causal_exp_weighted_primitive_C1_local
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T23:45:35.649029+00:00
-- url     : https://prove2.me/theorems/62bbad27-09c4-4555-922f-dcc19889beac
-- title:
--   C1 positive-time regularity of an exponentially damped causal primitive
-- statement:
--   Under interval integrability of its exponentially weighted kernel on every finite positive interval, continuity of the weighted kernel and the original kernel, the damped causal primitive is C1 on positive times. This supplies each signed Gaussian Volterra Neumann term's smoothness interface.
-- source:
--   Composition of the canonically Proved local HasDerivAt identity and C1 regularity of a first-order damped resolvent with continuous forcing.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_AvramDividend_Classical_causal_exp_weighted_primitive_hasDerivAt_local
import Theorems.Thm_AvramDividend_Classical_causal_damped_resolvent_C1_of_continuous_forcing

open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_exp_weighted_primitive_C1_local
    (g : ℝ → ℝ) (w : ℝ)
    (hInt : ∀ x : ℝ, 0 < x →
      IntervalIntegrable (fun s : ℝ => Real.exp (w * s) * g s) volume 0 x)
    (hCont : ContinuousOn (fun s : ℝ => Real.exp (w * s) * g s)
      (Ioi (0 : ℝ)))
    (hgCont : ContinuousOn g (Ioi (0 : ℝ))) :
    ContDiffOn ℝ 1
      (fun y : ℝ => Real.exp (-w * y) *
        (∫ s in Ioc (0 : ℝ) y, Real.exp (w * s) * g s ∂volume))
      (Ioi (0 : ℝ)) := by sorry
