-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f4_turn16_first_order_exp_comparison_v2
-- name    : AvramDividend.Classical.avram_p4_f4_turn16_first_order_exp_comparison_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T09:44:52.835499+00:00
-- url     : https://prove2.me/theorems/2893f25c-fbcd-4371-a045-ffb280f028ac
-- title:
--   One-sided first-order differential exponential comparison
-- statement:
--   If f is continuous on a closed positive half-ray, differentiable on its interior and f' ≤ r f, then f(x) ≤ f(a) exp(r(x-a)).
-- source:
--   A standard integrating-factor consequence of antitoneOn_of_deriv_nonpos in pinned Mathlib. Supports the two-stage factorised ODE supersolution comparison.

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open Set Filter Topology

noncomputable section

theorem AvramDividend.Classical.avram_p4_f4_turn16_first_order_exp_comparison_v2
    (f : ℝ → ℝ) (r a : ℝ)
    (hCont : ContinuousOn f (Ici a))
    (hDiff : DifferentiableOn ℝ f (Ioi a))
    (hDeriv : ∀ x : ℝ, a < x → deriv f x ≤ r * f x) :
    ∀ x : ℝ, a ≤ x → f x ≤ f a * Real.exp (r * (x - a)) := by sorry
