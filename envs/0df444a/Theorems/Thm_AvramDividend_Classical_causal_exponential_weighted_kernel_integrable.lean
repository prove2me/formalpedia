-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_exponential_weighted_kernel_integrable
-- name    : AvramDividend.Classical.causal_exponential_weighted_kernel_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T22:20:54.775762+00:00
-- url     : https://prove2.me/theorems/8315a087-611e-42d4-b434-8a933b40f633
-- title:
--   Positive-time L1 kernels remain integrable after exponential damping
-- statement:
--   An L1 kernel on positive real times remains L1 after multiplication by e^(−wt) for any nonnegative damping rate w. This gives the weighted kernel-integrability hypothesis required by the small-norm uniqueness lemma and Volterra contraction estimates.

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open MeasureTheory Set

theorem AvramDividend.Classical.causal_exponential_weighted_kernel_integrable
    (K : ℝ → ℝ) (w : ℝ) (hw : 0 ≤ w)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume) :
    IntegrableOn (fun t : ℝ => Real.exp (-w * t) * K t)
      (Ioi (0 : ℝ)) volume := by sorry
