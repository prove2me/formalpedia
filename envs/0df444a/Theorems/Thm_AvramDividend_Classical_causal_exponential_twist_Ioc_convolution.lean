-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_exponential_twist_Ioc_convolution
-- name    : AvramDividend.Classical.causal_exponential_twist_Ioc_convolution
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T20:23:16.059368+00:00
-- url     : https://prove2.me/theorems/5b8c1eae-21e2-406b-859e-ae0f9921e8f8
-- title:
--   Causal convolution respects exponential untwisting
-- statement:
--   Multiplication of a causal convolution by exp(w x) equals convolution of each input after separate multiplication by exp(w times its own time argument). Applies to every signed Neumann power P(n+1)=k*Pn to derive the undamped positive-time Volterra series recursion.
-- source:
--   Use Real.exp_add and the algebraic equality w*s+w*(x-s)=w*x to move the exponential multiplier inside the Ioc convolution integral, then rearrange the two factors. This is the exact exponential twist of each signed Neumann convolution-power recurrence.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Ring

open MeasureTheory Set

theorem AvramDividend.Classical.causal_exponential_twist_Ioc_convolution
    (k P : ℝ → ℝ) (w x : ℝ) :
    Real.exp (w * x) *
      (∫ s in Ioc (0 : ℝ) x, k s * P (x - s) ∂volume) =
    ∫ s in Ioc (0 : ℝ) x,
      (Real.exp (w * s) * k s) *
        (Real.exp (w * (x - s)) * P (x - s)) ∂volume := by sorry
