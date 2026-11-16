-- Prove2me | Theorems.Thm_BranchSummability_gaussian_resolvent_bound
-- name    : BranchSummability.gaussian_resolvent_bound
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-16T05:57:34.10523+00:00
-- url     : https://prove2.me/theorems/dfeaa64a-fd90-4aa3-a3d9-5ca49fc44376
-- title:
--   gaussian resolvent bound
-- statement:
--   For real g and t>0, $$e^{-g^2t}\le\frac{1+t^{-1}}{1+g^2}.$$ This comparison bounds a Gaussian by a summable resolvent weight.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandão Bueno. Analytic completion of conditional Branch certificate, 16 Nov 2026. No novelty claim.

import Mathlib
open Real

theorem BranchSummability.gaussian_resolvent_bound (g t : ℝ) (ht : 0 < t) :
    Real.exp (-g^2*t) ≤ (1+t⁻¹)/(1+g^2) := by sorry
