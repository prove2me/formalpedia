-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_05_tent_weighted_interval_domination
-- name    : AvramDividend.Classical.avram_wave3_05_tent_weighted_interval_domination
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:48:23.731022+00:00
-- url     : https://prove2.me/theorems/52f9529f-d63b-4857-bdfb-c58619db368b
-- title:
--   Weighted absolute domination of the genuine small-jump quadratic Taylor tent
-- statement:
--   For nonnegative jump magnitude r and Laplace weight θ, the exponential discount at reserve x times the absolute backward second-order Taylor tent integral is bounded by the tent integral with absolute integrand and discount evaluated at the shifted state x−s. Exact interval integrability requirements are explicit, permitting application to the C² positive-state Gaussian scale function.
-- source:
--   Pinned Mathlib and exact remote source probe 9b307a2b-a964-475f-8647-217dba7d9074 on 30 October 2026.

import Mathlib

open MeasureTheory Set intervalIntegral

theorem AvramDividend.Classical.avram_wave3_05_tent_weighted_interval_domination
    (F : ℝ → ℝ) (x r θ : ℝ)
    (hr : 0 ≤ r) (hθ : 0 ≤ θ)
    (hI : IntervalIntegrable (fun s : ℝ => (r - s) * F (x - s)) volume 0 r)
    (hJ : IntervalIntegrable
      (fun s : ℝ => (r - s) * Real.exp (-θ * (x - s)) * |F (x - s)|)
      volume 0 r) :
    Real.exp (-θ * x) *
      |∫ s in (0 : ℝ)..r, (r - s) * F (x - s)| ≤
      ∫ s in (0 : ℝ)..r,
        (r - s) * Real.exp (-θ * (x - s)) * |F (x - s)| := by sorry
