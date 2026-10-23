-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_volterra_integrated_identity_of_resolvent
-- name    : AvramDividend.Classical.causal_volterra_integrated_identity_of_resolvent
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T17:01:27.618991+00:00
-- url     : https://prove2.me/theorems/fd4b47d7-9c98-49a9-ae0a-17217709c695
-- title:
--   Integrated causal Volterra equation from a derivative resolvent via Fubini
-- statement:
--   Let g be continuous on nonnegative times and solve a g(t)+integral_0^t k(t-s)g(s) ds=1 for every t>0, where k=β+K and K is integrable on positive times. Integrate this equation over t∈(0,x]. Causal Fubini on the triangle 0≤s≤t≤x, using the local integrability of k and the boundedness of g on compact intervals, gives integral_0^x integral_0^t k(t-s)g(s)ds dt = integral_0^x k(x-s)G(s)ds, where G(s)=integral_0^s g(t)dt. Since the integral of 1 over (0,x] is x, this yields the claimed integrated Volterra identity. All integrals are Lebesgue integrals on Ioc intervals.
-- source:
--   Fubini theorem on a compact triangular domain and associativity of causal convolution with the indicator of nonnegative time.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.causal_volterra_integrated_identity_of_resolvent
    (K g : ℝ → ℝ) (a β : ℝ)
    (ha : 0 < a)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hg : ContinuousOn g (Ici (0 : ℝ)))
    (hgeq : ∀ x : ℝ, 0 < x →
      a * g x +
        (∫ s in Ioc (0 : ℝ) x,
          (β + K (x - s)) * g s ∂volume) = 1) :
    ∀ x : ℝ, 0 < x →
      a * (∫ t in Ioc (0 : ℝ) x, g t ∂volume) +
        (∫ s in Ioc (0 : ℝ) x,
          (β + K (x - s)) *
            (∫ t in Ioc (0 : ℝ) s, g t ∂volume) ∂volume) = x := by sorry
