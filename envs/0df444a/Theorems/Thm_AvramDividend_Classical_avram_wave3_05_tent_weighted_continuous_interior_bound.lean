-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_05_tent_weighted_continuous_interior_bound
-- name    : AvramDividend.Classical.avram_wave3_05_tent_weighted_continuous_interior_bound
-- status  : Open
-- author  : @WillR
-- created : 2026-10-30T09:53:10.24086+00:00
-- url     : https://prove2.me/theorems/7b6aa67e-ef9c-4ceb-843a-75b597ca84fd
-- title:
--   Quadratic weighted Gaussian Taylor remainder bound with local integrability derived from C2
-- statement:
--   The original Gaussian compensated small-jump Taylor kernel has a quadratic jump-size bound after integration against an exponential state weight. Continuity of the source second-derivative on positive reserves automatically gives both previously conditional interval-integrability premises. Remaining hR captures global absolute remainder integrability, to be derived separately from joint measurability and domination.
-- source:
--   Pinned remote Lean private candidate job 2284c333-92f8-45c9-98d1-6592cc043f4e passed to sentinel 30 October 2026. Based on positive-tail convolution mass and source Gaussian C2.

import Mathlib

open MeasureTheory Set intervalIntegral

theorem AvramDividend.Classical.avram_wave3_05_tent_weighted_continuous_interior_bound
    (F : ℝ → ℝ) (r θ : ℝ) (hr : 0 ≤ r) (hθ : 0 ≤ θ)
    (hFc : ContinuousOn F (Ioi (0 : ℝ)))
    (hF : Integrable
      (fun u : ℝ => Real.exp (-θ * u) * |F u|) volume)
    (hR : IntegrableOn
      (fun x : ℝ => Real.exp (-θ * x) *
        |∫ s in (0 : ℝ)..r, (r - s) * F (x - s)|)
      (Ioi r) volume) :
    (∫ x in Ioi r,
      Real.exp (-θ * x) *
        |∫ s in (0 : ℝ)..r, (r - s) * F (x - s)|) ≤
      (r ^ 2 / 2) *
        (∫ u : ℝ, Real.exp (-θ * u) * |F u|) := by sorry
