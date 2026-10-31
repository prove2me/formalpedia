-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_05_tent_local_interval_integrability
-- name    : AvramDividend.Classical.avram_wave3_05_tent_local_interval_integrability
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:37:46.045668+00:00
-- url     : https://prove2.me/theorems/96ff645f-e123-44ed-88ae-0b43429a579c
-- title:
--   Local integrability of both Gaussian compensated Taylor tent kernels on positive reserves
-- statement:
--   For every continuous second-derivative kernel on strictly positive reserves and every backward segment of jump length r shorter than reserve x, both the signed and exponentially weighted absolute compensated quadratic Taylor kernels are interval integrable. The proof uses local C² continuity and positivity of all translated reserve arguments.
-- source:
--   Exact pinned Mathlib, genuine Gaussian source generator; remote private proof elaborated 30 October 2026, job 10d2f85c-70ed-45cd-b19e-b450e2ffb6ce.

import Mathlib

open MeasureTheory Set intervalIntegral

theorem AvramDividend.Classical.avram_wave3_05_tent_local_interval_integrability
    (F : ℝ → ℝ) (hF : ContinuousOn F (Ioi (0 : ℝ)))
    (r x θ : ℝ) (hr : 0 ≤ r) (hx : r < x) :
    IntervalIntegrable (fun s : ℝ => (r - s) * F (x - s)) volume 0 r ∧
      IntervalIntegrable (fun s : ℝ =>
        (r - s) * Real.exp (-θ * (x - s)) * |F (x - s)|)
        volume 0 r := by sorry
