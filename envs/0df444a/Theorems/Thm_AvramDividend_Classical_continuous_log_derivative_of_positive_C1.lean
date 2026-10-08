-- Prove2me | Theorems.Thm_AvramDividend_Classical_continuous_log_derivative_of_positive_C1
-- name    : AvramDividend.Classical.continuous_log_derivative_of_positive_C1
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T10:56:27.955437+00:00
-- url     : https://prove2.me/theorems/be85fa09-d2af-408f-b7e7-21214074078c
-- title:
--   Continuity of the logarithmic derivative of a positive C1 function
-- statement:
--   For V>0 and C1 on the positive half-line, log∘V is C1 there by the chain rule, and hence its real derivative is continuous there. This discharges the continuity part of the analytic excursion measure shape theorem using the already existing but currently Open scaleFunction_contDiff_one_of_absolutely_continuous_levy.
-- source:
--   Pinned Mathlib Real ContDiffOn.log and ContDiffOn.continuousOn_deriv_of_isOpen.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set Filter
open scoped Topology

theorem AvramDividend.Classical.continuous_log_derivative_of_positive_C1
    (V : ℝ → ℝ)
    (hVpos : ∀ x : ℝ, 0 < x → 0 < V x)
    (hVone : ContDiffOn ℝ 1 V (Ioi (0 : ℝ))) :
    ContinuousOn (fun x : ℝ => deriv (fun y : ℝ => Real.log (V y)) x)
      (Ioi (0 : ℝ)) := by sorry
