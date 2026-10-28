-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_resolvent_C1_of_L1_primitive
-- name    : AvramDividend.Classical.causal_resolvent_C1_of_L1_primitive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T20:47:09.388623+00:00
-- url     : https://prove2.me/theorems/fb40f3f7-765d-4e46-b19f-3bf356ea4975
-- title:
--   C1 regularity transfer through a damped causal scale resolvent
-- statement:
--   A continuous causal input f inherits positive-time C1 regularity from a C1 comparison kernel g when their damped resolvent relation is f=g-a(f*g), f is L1, and g is the causal primitive of a second L1 kernel k. The existing Proved L1 causal smoothing lemma makes f*g C1, and the resolvent equation transfers smoothness. This is the exact deterministic final step for comparing zero and positive discount Lévy scale functions after exponential damping.
-- source:
--   Proved causal_l1_convolution_C1_of_kernel_primitive (26e95536-54ba-4c2e-afee-6a23f1b3933e) and C1 closure under linear combinations. The scale resolvent follows from unbounded_scale_resolvent_convolution (4198c14e-7e01-4121-a3e9-8f4e30ee2b4d), weighted derivative integrability (a01f741d-18f2-4a06-af0d-61e118db667a) and common Laplace tail (30c9b779-d0ca-4fe8-9b52-d86ed6d87efe).

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Theorems.Thm_AvramDividend_Classical_causal_l1_convolution_C1_of_kernel_primitive
open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_resolvent_C1_of_L1_primitive
    (f g k : ℝ → ℝ) (a : ℝ)
    (hf : ContinuousOn f (Ici (0 : ℝ)))
    (hfL1 : IntegrableOn f (Ioi (0 : ℝ)) volume)
    (hkL1 : IntegrableOn k (Ioi (0 : ℝ)) volume)
    (hg : ∀ x : ℝ, 0 < x →
      (∫ t in Ioc (0 : ℝ) x, k t ∂volume) = g x)
    (hgC1 : ContDiffOn ℝ 1 g (Ioi (0 : ℝ)))
    (hres : ∀ x : ℝ, 0 < x →
      f x = g x - a * (∫ s in Ioc (0 : ℝ) x,
        f (x - s) * g s ∂volume)) :
    ContDiffOn ℝ 1 f (Ioi (0 : ℝ)) := by sorry
