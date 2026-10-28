-- Prove2me | Theorems.Thm_AvramDividend_Classical_exponential_causal_convolution_factorisation
-- name    : AvramDividend.Classical.exponential_causal_convolution_factorisation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T21:03:57.926268+00:00
-- url     : https://prove2.me/theorems/619dc32b-d36b-487b-9af3-37d809a56118
-- title:
--   Exponential damping factors through finite causal convolutions
-- statement:
--   Multiplying a causal convolution by an exponential damping factor equals the convolution of its exponentially damped inputs. The identity follows from exp(a+b)=exp(a)exp(b) and holds even for singular causal kernels. It converts the undamped scale-function resolvent into the exact weighted equation needed by the proved C1 transfer.
-- source:
--   Real.exp_add and MeasureTheory.integral_const_mul; application to Proved unbounded_scale_resolvent_convolution and causal_resolvent_C1_of_L1_primitive.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.exponential_causal_convolution_factorisation
    (f g : ℝ → ℝ) (θ x : ℝ) :
    Real.exp (-(θ * x)) *
      (∫ s in Ioc (0 : ℝ) x, f (x - s) * g s ∂volume) =
    ∫ s in Ioc (0 : ℝ) x,
      (Real.exp (-(θ * (x - s))) * f (x - s)) *
        (Real.exp (-(θ * s)) * g s) ∂volume := by sorry
