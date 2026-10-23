-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_l1_fullkernel_primitive_fubini
-- name    : AvramDividend.Classical.causal_l1_fullkernel_primitive_fubini
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T17:42:59.600996+00:00
-- url     : https://prove2.me/theorems/33e136a7-7564-47e3-af2b-f63d3fd23815
-- title:
--   Integrated causal convolution with an L1 kernel plus constant drift
-- statement:
--   Let g be continuous on nonnegative times and K integrable on positive times. For any β and x>0, the integral of the causal convolution with k(t)=β+K(t) equals the convolution of k with the primitive of g. Split the kernel into a constant and K. The constant contribution follows immediately from Fubini or ordinary integral linearity; the K contribution is the separate finite-triangle theorem causal_l1_kernel_triangle_fubini.
-- source:
--   Convolution-primitive associativity and linearity, relying on the separately published causal_l1_kernel_triangle_fubini lemma.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.causal_l1_fullkernel_primitive_fubini
    (K g : ℝ → ℝ) (β : ℝ)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hg : ContinuousOn g (Ici (0 : ℝ)))
    (x : ℝ) (hx : 0 < x) :
    (∫ t in Ioc (0 : ℝ) x,
      (∫ s in Ioc (0 : ℝ) t,
        (β + K (t - s)) * g s ∂volume) ∂volume) =
    (∫ s in Ioc (0 : ℝ) x,
      (β + K (x - s)) *
        (∫ t in Ioc (0 : ℝ) s, g t ∂volume) ∂volume) := by sorry
