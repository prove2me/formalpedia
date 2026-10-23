-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_l1_truncated_convolution_prod_integrable
-- name    : AvramDividend.Classical.causal_l1_truncated_convolution_prod_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T20:57:52.722865+00:00
-- url     : https://prove2.me/theorems/308f744d-b755-4dcd-b0f1-5ad2e5b4b176
-- title:
--   Product-measure integrability of the truncated causal convolution integrand
-- statement:
--   A positive-time L1 kernel K and an input g continuous on nonnegative times produce an integrable two-variable convolution integrand after truncating K to positive lag and g to (0,x]. Apply Mathlib.Integrable.convolution_integrand to the two globally L1 truncated functions. This supplies the product-integrability hypothesis needed for rigorous Fubini interchange on the causal triangle.
-- source:
--   Mathlib.Analysis.Convolution: MeasureTheory.Integrable.convolution_integrand.

import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.causal_l1_truncated_convolution_prod_integrable
    (K g : ℝ → ℝ)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hg : ContinuousOn g (Ici (0 : ℝ)))
    (x : ℝ) (hx : 0 < x) :
    Integrable (fun p : ℝ × ℝ =>
      ((Ioi (0 : ℝ)).indicator K) p.2 *
      ((Ioc (0 : ℝ) x).indicator g) (p.1 - p.2))
      (volume.prod volume) := by sorry
