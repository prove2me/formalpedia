-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_full_kernel_locally_bounded_input_integrable
-- name    : AvramDividend.Classical.causal_full_kernel_locally_bounded_input_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T22:39:13.777994+00:00
-- url     : https://prove2.me/theorems/42cc92f1-43a9-420d-b813-2e15791b1841
-- title:
--   Locally bounded input is integrable against the drift-plus-L1 Volterra kernel
-- statement:
--   For any β and positive-time integrable causal K, if V is continuous on positive times and locally bounded near zero, then the product (β+K(x−s))V(s) is integrable over (0,x] for each x>0. It separates the constant-drift part from the L1 causal part and supports subtraction of two Volterra solution identities.

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_causal_l1_kernel_locally_bounded_input_integrable
open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_full_kernel_locally_bounded_input_integrable
    (K V : ℝ → ℝ) (β : ℝ)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hVc : ContinuousOn V (Ioi (0 : ℝ)))
    (hVb : ∀ R : ℝ, 0 < R →
      ∃ C : ℝ, ∀ s : ℝ, s ∈ Ioc (0 : ℝ) R → |V s| ≤ C)
    (x : ℝ) (hx : 0 < x) :
    IntegrableOn (fun s : ℝ => (β + K (x - s)) * V s)
      (Ioc (0 : ℝ) x) volume := by sorry
