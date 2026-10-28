-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_resolvent_C1_of_exponential_weighting
-- name    : AvramDividend.Classical.causal_resolvent_C1_of_exponential_weighting
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T21:11:04.972982+00:00
-- url     : https://prove2.me/theorems/937ca940-269a-42af-90ac-a4396f797b3e
-- title:
--   Undamped C1 regularity from an exponentially weighted Volterra resolvent
-- statement:
--   The exact deterministic exponential-damping bridge. If an undamped causal resolvent f=g-a(f*g) has a C1 comparison function g, and the damped input f_theta and damped derivative kernel are L1 with the latter primitive equal to damped g, then f is C1 on positive times. No global L1 assumption is imposed on the original scale functions. The proof factors the weight through convolution and undamps the proved L1 resolvent.
-- source:
--   Proved causal_resolvent_C1_of_L1_primitive and exponential_causal_convolution_factorisation; elementary calculus of exp.

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Theorems.Thm_AvramDividend_Classical_causal_resolvent_C1_of_L1_primitive
import Theorems.Thm_AvramDividend_Classical_exponential_causal_convolution_factorisation
open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_resolvent_C1_of_exponential_weighting
    (f g k : ℝ → ℝ) (a θ : ℝ)
    (hf : ContinuousOn f (Ici (0 : ℝ)))
    (hfL1 : IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) * f x)
      (Ioi (0 : ℝ)) volume)
    (hkL1 : IntegrableOn k (Ioi (0 : ℝ)) volume)
    (hprim : ∀ x : ℝ, 0 < x →
      (∫ t in Ioc (0 : ℝ) x, k t ∂volume) =
        Real.exp (-(θ * x)) * g x)
    (hgC1 : ContDiffOn ℝ 1 g (Ioi (0 : ℝ)))
    (hres : ∀ x : ℝ, 0 < x →
      f x = g x - a *
        (∫ s in Ioc (0 : ℝ) x, f (x - s) * g s ∂volume)) :
    ContDiffOn ℝ 1 f (Ioi (0 : ℝ)) := by sorry
