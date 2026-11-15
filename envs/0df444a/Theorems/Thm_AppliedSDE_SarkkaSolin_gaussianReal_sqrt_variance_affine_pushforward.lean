-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_gaussianReal_sqrt_variance_affine_pushforward
-- name    : AppliedSDE.SarkkaSolin.gaussianReal_sqrt_variance_affine_pushforward
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T12:05:45.393255+00:00
-- url     : https://prove2.me/theorems/f400ac2f-e487-4252-b386-456f1cc86051
-- title:
--   Affine square-root-variance representation of a Gaussian measure
-- statement:
--   For positive diffusion variance q, nonnegative elapsed time h and any drift b, the pushforward of a standard normal law by z maps to sqrt(q*h)*z + y+b*h is precisely the Gaussian law with mean y+b*h and variance (q*h).toNNReal. This remains valid at h=0 where both sides become a Dirac measure.
-- source:
--   Sarkka and Solin (2019), Gaussian transition kernel, Chapter 5; published target c050c09d-fba6-4fce-9645-3b7e9e91265e.

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

theorem AppliedSDE.SarkkaSolin.gaussianReal_sqrt_variance_affine_pushforward
    (b q y h : ℝ) (hq : 0 < q) (hh : 0 ≤ h) :
    (gaussianReal 0 1).map
      (fun z : ℝ => Real.sqrt (q * h) * z + (y + b * h)) =
    gaussianReal (y + b * h) (q * h).toNNReal := by
  sorry
