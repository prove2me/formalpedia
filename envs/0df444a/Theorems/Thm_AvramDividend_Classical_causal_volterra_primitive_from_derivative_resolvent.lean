-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_volterra_primitive_from_derivative_resolvent
-- name    : AvramDividend.Classical.causal_volterra_primitive_from_derivative_resolvent
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T16:18:33.876736+00:00
-- url     : https://prove2.me/theorems/9235abfe-de54-4517-bbbf-28a146a7067c
-- title:
--   Primitive of a continuous causal resolvent solves the integrated Volterra equation
-- statement:
--   Assume g is continuous on nonnegative times and satisfies a g(x)+integral_0^x(β+K(x-s))g(s) ds=1 for x>0, with a>0 and K L1 on positive times. Define G(x)=integral_0^x g(t) dt for x≥0, and extend arbitrarily to negative x. The fundamental theorem of calculus gives G∈C1 on positive times, and continuity on compact intervals gives its local boundedness. Integrating the derivative-resolvent identity over [0,x], Fubini/Tonelli for locally bounded g and the locally integrable causal kernel yields integral_0^x integral_0^t (β+K(t-s))g(s)ds dt = integral_0^x (β+K(x-s))G(s)ds. Consequently aG(x)+integral_0^x(β+K(x-s))G(s)ds=x. This lemma isolates the primitive/Fubini passage and is independent of the original existence theorem.
-- source:
--   Fundamental theorem of calculus and Fubini theorem for integrable causal Volterra convolution on compact triangles.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.causal_volterra_primitive_from_derivative_resolvent
    (K g : ℝ → ℝ) (a β : ℝ)
    (ha : 0 < a)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hg : ContinuousOn g (Ici (0 : ℝ)))
    (hgeq : ∀ x : ℝ, 0 < x →
      a * g x +
        (∫ s in Ioc (0 : ℝ) x,
          (β + K (x - s)) * g s ∂volume) = 1) :
    ∃ G : ℝ → ℝ,
      ContDiffOn ℝ 1 G (Ioi (0 : ℝ)) ∧
      (∀ R : ℝ, 0 < R →
        ∃ C : ℝ, ∀ x : ℝ, x ∈ Ioc (0 : ℝ) R → |G x| ≤ C) ∧
      (∀ x : ℝ, 0 < x →
        a * G x +
          (∫ s in Ioc (0 : ℝ) x,
            (β + K (x - s)) * G s ∂volume) = x) := by sorry
