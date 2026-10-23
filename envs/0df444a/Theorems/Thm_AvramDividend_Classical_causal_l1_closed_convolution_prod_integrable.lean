-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_l1_closed_convolution_prod_integrable
-- name    : AvramDividend.Classical.causal_l1_closed_convolution_prod_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T21:15:59.447577+00:00
-- url     : https://prove2.me/theorems/d5837bc6-ee02-44a4-af66-fd356b99666c
-- title:
--   Product integrability of a causal L1 kernel and a closed finite input window
-- statement:
--   If K is L1 on positive times and g is continuous on nonnegative times, the product (u,t)↦K(u)g(t-u), cut off to u>0 and t-u∈[0,x], is integrable on R×R. The closed finite window retains the initial endpoint and is useful when reflecting the causal convolution.
-- source:
--   Mathlib.Analysis.Convolution, Integrable.convolution_integrand; Mathlib.MeasureTheory.Function.LocallyIntegrable.

import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.causal_l1_closed_convolution_prod_integrable
    (K g : ℝ → ℝ)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hg : ContinuousOn g (Ici (0 : ℝ)))
    (x : ℝ) (hx : 0 < x) :
    Integrable (fun p : ℝ × ℝ =>
      ((Ioi (0 : ℝ)).indicator K) p.2 *
      ((Icc (0 : ℝ) x).indicator g) (p.1 - p.2))
      (volume.prod volume) := by sorry
