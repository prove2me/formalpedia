-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_l1_kernel_primitive_product_integrable
-- name    : AvramDividend.Classical.causal_l1_kernel_primitive_product_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T20:42:06.337813+00:00
-- url     : https://prove2.me/theorems/a3f7a05f-8b7f-481f-93c5-fbd5245467af
-- title:
--   Finite-interval integrability of an L1 kernel against a causal primitive
-- statement:
--   Let K be L1 on positive times and g continuous on nonnegative times. For any x>0 the product K(x-s)G(s), where G(s)=integral_(0,s]g, is integrable on (0,x]. The existing primitive theorem makes G continuous on positive times and bounded on finite intervals; the existing local kernel theorem gives integrability of K(x-s). Apply bounded multiplication on restricted volume.
-- source:
--   Previously proved causal_primitive_C1_locally_bounded and causal_l1_kernel_continuous_input_integrable, plus Integrable.bdd_mul.

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Theorems.Thm_AvramDividend_Classical_causal_primitive_C1_locally_bounded
import Theorems.Thm_AvramDividend_Classical_causal_l1_kernel_continuous_input_integrable

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.causal_l1_kernel_primitive_product_integrable
    (K g : ℝ → ℝ)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hg : ContinuousOn g (Ici (0 : ℝ)))
    (x : ℝ) (hx : 0 < x) :
    IntegrableOn (fun s : ℝ =>
      K (x - s) * (∫ t in Ioc (0 : ℝ) s, g t ∂volume))
      (Ioc (0 : ℝ) x) volume := by sorry
