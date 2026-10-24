-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_reflected_kernel_right_interval_integrable
-- name    : AvramDividend.Classical.causal_reflected_kernel_right_interval_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T14:31:04.254799+00:00
-- url     : https://prove2.me/theorems/96a6ea97-883f-4d33-9e97-cd5d73f6c30f
-- title:
--   Causal reflected kernel retains interval integrability on the right split
-- statement:
--   If the kernel is integrable over the initial interval from zero to x-u, then its reflected translate s ↦ κ(x-s) is integrable over the right-hand interval from u to x. This is precisely the reflected-kernel interval integrability required by the Gaussian convolution-power cutoff induction, without kernel boundedness at zero.
-- source:
--   Pinned Mathlib IntervalIntegrable.comp_sub_left composed with IntervalIntegrable.symm, simplifying the reflected endpoints.

import Mathlib.Analysis.Convolution

open MeasureTheory Set

theorem AvramDividend.Classical.causal_reflected_kernel_right_interval_integrable
    (κ : ℝ → ℝ) (x u : ℝ)
    (hκ : IntervalIntegrable κ volume 0 (x - u)) :
    IntervalIntegrable (fun s : ℝ => κ (x - s)) volume u x := by sorry
