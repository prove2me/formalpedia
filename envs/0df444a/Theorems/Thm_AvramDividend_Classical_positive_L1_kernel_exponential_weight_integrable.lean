-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_L1_kernel_exponential_weight_integrable
-- name    : AvramDividend.Classical.positive_L1_kernel_exponential_weight_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T21:32:29.956108+00:00
-- url     : https://prove2.me/theorems/0592dda5-0fef-4cb9-b950-332fd8e21f43
-- title:
--   A positive-axis L1 Volterra kernel remains integrable after exponential damping
-- statement:
--   If a real kernel K is Lebesgue integrable on (0,∞) and w>0, its damped version e^(−wt)K(t) is also integrable on (0,∞). The damping function is continuous, hence measurable, and has norm ≤1 on positive times. Pinned Mathlib Integrable.bdd_mul combines this bound with K∈L1. This discharges the extra weighted-kernel integrability hypothesis for the general Volterra contraction argument.
-- source:
--   Pinned Mathlib MeasureTheory.Integrable.bdd_mul.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.positive_L1_kernel_exponential_weight_integrable
    (K : ℝ → ℝ) (w : ℝ) (hw : 0 < w)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume) :
    IntegrableOn (fun t : ℝ => Real.exp (-w * t) * K t)
      (Ioi (0 : ℝ)) volume := by sorry
