-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_l1_kernel_continuous_input_integrable
-- name    : AvramDividend.Classical.causal_l1_kernel_continuous_input_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T17:51:30.85152+00:00
-- url     : https://prove2.me/theorems/f78c1857-b550-4702-ae83-48d3155e0c77
-- title:
--   Local integrability of an L1 causal kernel multiplied by a continuous input
-- statement:
--   If K is L1 on positive times and g is continuous on nonnegative times, the integrand s↦K(x-s)g(s) is integrable on (0,x] for every x>0. Extend K by zero outside positive times, reflect/translate its integrable extension to x-s, and multiply by the bounded continuous factor g on compact [0,x]. The discrepancy at s=x is a null singleton.
-- source:
--   Pinned Mathlib: Integrable.comp_sub_left, Integrable.bdd_mul, integrable_indicator_iff, compactness of Icc.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.causal_l1_kernel_continuous_input_integrable
    (K g : ℝ → ℝ)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hg : ContinuousOn g (Ici (0 : ℝ))) :
    ∀ x : ℝ, 0 < x →
      IntegrableOn (fun s : ℝ => K (x - s) * g s) (Ioc (0 : ℝ) x) volume := by sorry
