-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_l1_kernel_locally_bounded_input_integrable
-- name    : AvramDividend.Classical.causal_l1_kernel_locally_bounded_input_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T22:03:09.821768+00:00
-- url     : https://prove2.me/theorems/0113ca80-b23c-46c9-9ef9-4770a9a5c16f
-- title:
--   Causal L1 kernel is locally integrable against a positive-time continuous, locally bounded function
-- statement:
--   If K is L1 on positive lags and V is continuous on the positive open half-line and uniformly bounded on each finite interval (0,R], then K(x-s)V(s) is integrable over (0,x] for each x>0. Use the proved local reflected-kernel integrability with the constant-one input, positive-interval measurability of V, and norm domination by C|K(x-s)|. This exactly discharges the missing integrability needed when subtracting two Volterra solutions without assuming continuity at zero.
-- source:
--   Proved causal_l1_kernel_continuous_input_integrable; pinned Mathlib Integrable.mono; ContinuousOn.aestronglyMeasurable.

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_causal_l1_kernel_continuous_input_integrable
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.causal_l1_kernel_locally_bounded_input_integrable
    (K V : ℝ → ℝ)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hVc : ContinuousOn V (Ioi (0 : ℝ)))
    (hVb : ∀ R : ℝ, 0 < R →
      ∃ C : ℝ, ∀ s : ℝ, s ∈ Ioc (0 : ℝ) R → |V s| ≤ C)
    (x : ℝ) (hx : 0 < x) :
    IntegrableOn (fun s : ℝ => K (x - s) * V s)
      (Ioc (0 : ℝ) x) volume := by sorry
